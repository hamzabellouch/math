import Mathlib
import OAI.Analysis.BiholderTransport.Duality.GeometricEnvelope
import OAI.Analysis.BiholderTransport.Coordinates.FiberLog

namespace OAI

noncomputable section

namespace WeakMTWTransport

namespace ParameterVariation

section
open Set Filter
open scoped Topology BigOperators

lemma abs_le_of_positive_barycentric {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m L : ι → ℝ} {U : ℝ} (hm : ∀ i, 0 < m i)
    (hs : ∑ i, m i = 1) (hcancel : ∑ i, m i * L i = 0)
    (hU : 0 ≤ U) (hupper : ∀ i, L i ≤ U) (i : ι) :
    |L i| ≤ U / m i := by
  have hmi : m i ≤ 1 := by
    rw [← hs]
    exact Finset.single_le_sum (fun j _ => (hm j).le) (Finset.mem_univ i)
  have hdef : ∑ j, m j * (U - L j) = U := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hs, hcancel]
    ring
  have hsingle : m i * (U - L i) ≤ U := by
    exact (Finset.single_le_sum (fun j _ => mul_nonneg (hm j).le (sub_nonneg.mpr (hupper j)))
      (Finset.mem_univ i)).trans_eq hdef
  apply (le_div_iff₀ (hm i)).mpr
  rw [mul_comm, ← abs_of_pos (hm i), ← abs_mul, abs_le]
  constructor
  · nlinarith [mul_nonneg (hm i).le hU]
  · exact (mul_le_mul_of_nonneg_left (hupper i) (hm i).le).trans
      (by nlinarith)

variable {ι E : Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma exists_span_projection_bound (a : ι → E) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : E, ∀ R : ℝ, 0 ≤ R →
      (∀ i, |inner ℝ (a i) x| ≤ R) →
      ‖(Submodule.span ℝ (range a)).starProjection x‖ ≤ K * R := by
  let S := Submodule.span ℝ (range a)
  let A : S →ₗ[ℝ] (ι → ℝ) := LinearMap.pi fun i =>
    (innerSL ℝ (a i)).toLinearMap.comp S.subtype
  have hinj : Function.Injective A := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    have horth : ∀ z ∈ S, inner ℝ z (x : E) = 0 := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
          obtain ⟨i,rfl⟩ := hz
          exact congrFun hx i
      | zero => simp
      | add x y hx hy hix hiy => simp [inner_add_left, hix, hiy]
      | smul r x hx hix => simp [inner_smul_left, hix]
    apply Subtype.ext
    exact inner_self_eq_zero.mp (horth x x.property)
  obtain ⟨K,hK,hA⟩ := A.injective_iff_antilipschitz.mp hinj
  refine ⟨K,by exact_mod_cast hK,?_⟩
  intro x R hR hx
  have heval (i : ι) : A (S.orthogonalProjectionOnto x) i = inner ℝ (a i) x := by
    change inner ℝ (a i) ((S.orthogonalProjectionOnto x : S) : E) = _
    exact S.inner_orthogonalProjectionOnto_eq_of_mem_left
      ⟨a i,Submodule.subset_span (mem_range_self i)⟩ x
  have hn : ‖A (S.orthogonalProjectionOnto x)‖ ≤ R := by
    apply (pi_norm_le_iff_of_nonneg hR).mpr
    intro i
    simpa only [heval i, Real.norm_eq_abs] using hx i
  have H := hA.le_mul_dist (S.orthogonalProjectionOnto x) 0
  simp only [map_zero, dist_zero_right] at H
  simpa only [Submodule.norm_coe, Submodule.starProjection_apply] using
    H.trans (mul_le_mul_of_nonneg_left hn K.coe_nonneg)

lemma exists_eventual_active_projection_bound {T : Type*} {l : Filter T}
    (a : ι → E) {m : ι → ℝ} (hm : ∀ i, 0 < m i)
    (hs : ∑ i, m i = 1) (hbar : ∑ i, m i • a i = 0)
    {h : T → ℝ} {d : T → E} {C : ℝ} (hC : 0 ≤ C)
    (hh : ∀ᶠ k in l, 0 ≤ h k)
    (ha : ∀ᶠ k in l, ∀ i, inner ℝ (a i) (d k) ≤ C*h k) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ k in l,
      ‖(Submodule.span ℝ (range a)).starProjection (d k)‖ ≤ K*h k := by
  classical
  let R := ∑ i, C/m i
  have hR : 0 ≤ R := Finset.sum_nonneg (fun i _ => div_nonneg hC (hm i).le)
  obtain ⟨K,hK,hproj⟩ := exists_span_projection_bound a
  refine ⟨K*R+1,by positivity,?_⟩
  filter_upwards [hh,ha] with k hhk hak
  have hcancel : ∑ i, m i * inner ℝ (a i) (d k) = 0 := by
    simpa only [sum_inner,real_inner_smul_left,inner_zero_left] using
      congrArg (fun x => inner ℝ x (d k)) hbar
  have hforms : ∀ i, |inner ℝ (a i) (d k)| ≤ R*h k := by
    intro i
    have H := abs_le_of_positive_barycentric hm hs hcancel (mul_nonneg hC hhk) hak i
    calc
      |inner ℝ (a i) (d k)| ≤ C*h k/m i := H
      _ = (C/m i)*h k := by ring
      _ ≤ R*h k := mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (fun j _ => div_nonneg hC (hm j).le) (Finset.mem_univ i)) hhk
  calc
    ‖(Submodule.span ℝ (range a)).starProjection (d k)‖ ≤ K*(R*h k) :=
      hproj (d k) (R*h k) (mul_nonneg hR hhk) hforms
    _ ≤ (K*R+1)*h k := by nlinarith only [hhk]

omit [FiniteDimensional ℝ E] in
lemma exists_eventual_active_linear_bound {T : Type*} {l : Filter T}
    (a : ι → E) (B : ι → ℝ) (Q : ι → E →L[ℝ] E →L[ℝ] ℝ)
    {h U : T → ℝ} {d : T → E} {e : ι → T → ℝ} {H K : ℝ}
    (hH : 0 ≤ H) (hK : 0 ≤ K)
    (hh : ∀ᶠ k in l, 0 < h k)
    (hd : ∀ᶠ k in l, ‖d k‖^2 ≤ K*h k)
    (hU : ∀ᶠ k in l, U k ≤ H*h k)
    (he : ∀ i, Tendsto (fun k => e i k/h k) l (𝓝 0))
    (hcontact : ∀ᶠ k in l, ∀ i,
      h k*B i+inner ℝ (a i) (d k)+Q i (d k) (d k)/2+e i k ≤ U k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k in l, ∀ i, inner ℝ (a i) (d k) ≤ C*h k := by
  classical
  let X := ∑ i, |B i|
  let Y := ∑ i, ‖Q i‖
  have hX : 0 ≤ X := Finset.sum_nonneg (fun i _ => abs_nonneg (B i))
  have hY : 0 ≤ Y := Finset.sum_nonneg (fun i _ => norm_nonneg (Q i))
  refine ⟨H+X+Y*K/2+1,by positivity,?_⟩
  have he' : ∀ᶠ k in l, ∀ i, -1 < e i k/h k :=
    eventually_all.mpr (fun i => (he i).eventually (lt_mem_nhds (by norm_num : (-1:ℝ)<0)))
  filter_upwards [hh,hd,hU,he',hcontact] with k hhk hdk hUk hek hck i
  have hiX : |B i| ≤ X := Finset.single_le_sum
    (fun j _ => abs_nonneg (B j)) (Finset.mem_univ i)
  have hiY : ‖Q i‖ ≤ Y := Finset.single_le_sum
    (fun j _ => norm_nonneg (Q j)) (Finset.mem_univ i)
  have hBi := mul_le_mul_of_nonneg_left ((neg_le_neg hiX).trans (neg_abs_le (B i))) hhk.le
  have hQi : |Q i (d k) (d k)| ≤ Y*K*h k := by
    calc
      |Q i (d k) (d k)| ≤ ‖Q i‖*‖d k‖*‖d k‖ := (Q i).le_opNorm₂ (d k) (d k)
      _ = ‖Q i‖*‖d k‖^2 := by ring
      _ ≤ ‖Q i‖*(K*h k) := mul_le_mul_of_nonneg_left hdk (norm_nonneg (Q i))
      _ ≤ Y*(K*h k) := mul_le_mul_of_nonneg_right hiY (mul_nonneg hK hhk.le)
      _ = Y*K*h k := by ring
  have hei : -h k ≤ e i k := by
    have HT := (lt_div_iff₀ hhk).mp (hek i)
    linarith only [HT]
  have hQi' := (abs_le.mp hQi).1
  nlinarith only [hck i,hUk,hBi,hQi',hei]

lemma projected_quadratic_lower (S : Submodule ℝ E)
    (Q : E →L[ℝ] E →L[ℝ] ℝ) (hQ : ∀ v ∈ Sᗮ, 0 ≤ Q v v) (x : E) :
    -‖Q‖ * (2 * ‖S.starProjection x‖ * ‖x‖ + ‖S.starProjection x‖ ^ 2) ≤ Q x x := by
  let e := S.starProjection x
  have hp := hQ (x-e) (S.sub_starProjection_mem_orthogonal x)
  simp only [map_sub, sub_apply] at hp
  have h1 := (abs_le.mp (show |Q x e| ≤ ‖Q‖*‖x‖*‖e‖ from Q.le_opNorm₂ x e)).1
  have h2 := (abs_le.mp (show |Q e x| ≤ ‖Q‖*‖e‖*‖x‖ from Q.le_opNorm₂ e x)).1
  have h3 := (abs_le.mp (show |Q e e| ≤ ‖Q‖*‖e‖*‖e‖ from Q.le_opNorm₂ e e)).2
  change -‖Q‖ * (2*‖e‖*‖x‖+‖e‖^2) ≤ Q x x
  nlinarith only [hp,h1,h2,h3]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma norm_tendsto_zero_of_sq_bound {T : Type*} {l : Filter T}
    {h : T → ℝ} {d : T → E} {K : ℝ}
    (hh : Tendsto h l (𝓝 0))
    (hb : ∀ᶠ k in l, ‖d k‖^2 ≤ K*h k) :
    Tendsto (fun k => ‖d k‖) l (𝓝 0) := by
  have H := squeeze_zero' (Eventually.of_forall (fun k => sq_nonneg ‖d k‖)) hb
    (show Tendsto (fun k => K*h k) l (𝓝 0) by simpa using hh.const_mul K)
  simpa only [Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using H.sqrt

lemma weighted_parameter_bound {T : Type*} {l : Filter T} [l.NeBot]
    (a : ι → E) (B : ι → ℝ) (Q : ι → E →L[ℝ] E →L[ℝ] ℝ)
    {m : ι → ℝ} (hm : ∀ i, 0 < m i) (hs : ∑ i, m i = 1)
    (hbar : ∑ i, m i • a i = 0)
    {h U e0 : T → ℝ} {d : T → E} {e : ι → T → ℝ} {K D : ℝ}
    (hK : 0 ≤ K) (hh : ∀ᶠ k in l, 0 < h k) (hh0 : Tendsto h l (𝓝 0))
    (hd : ∀ᶠ k in l, ‖d k‖^2 ≤ K*h k)
    (he : ∀ i, Tendsto (fun k => e i k/h k) l (𝓝 0))
    (he0 : Tendsto (fun k => e0 k/h k) l (𝓝 0))
    (hupper : ∀ᶠ k in l, U k ≤ h k*D+e0 k)
    (hcontact : ∀ᶠ k in l, ∀ i,
      h k*B i+inner ℝ (a i) (d k)+Q i (d k) (d k)/2+e i k ≤ U k)
    (hQ : ∀ v ∈ (Submodule.span ℝ (range a))ᗮ, 0 ≤ (∑ i, m i • Q i) v v) :
    ∑ i, m i*B i ≤ D := by
  classical
  let S := Submodule.span ℝ (range a)
  let Qt := ∑ i, m i • Q i
  have hU : ∀ᶠ k in l, U k ≤ (|D|+1)*h k := by
    filter_upwards [hh,hupper,he0.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))]
      with k hhk huk hek
    have he' := (div_lt_iff₀ hhk).mp hek
    have hD := mul_le_mul_of_nonneg_left (le_abs_self D) hhk.le
    nlinarith only [huk,he',hD]
  obtain ⟨C,hC,hlinear⟩ := exists_eventual_active_linear_bound a B Q
    (by positivity : 0 ≤ |D|+1) hK hh hd hU he hcontact
  obtain ⟨Kp,hKp,hproj⟩ := exists_eventual_active_projection_bound a hm hs hbar hC
    (hh.mono fun _ hk => hk.le) hlinear
  let δ := fun k => ‖Qt‖*(2*Kp*‖d k‖+Kp^2*h k)
  have hd0 := norm_tendsto_zero_of_sq_bound hh0 hd
  have hδ0 : Tendsto δ l (𝓝 0) := by
    simpa only [mul_zero,add_zero,δ] using
      ((hd0.const_mul (2*Kp)).add (hh0.const_mul (Kp^2))).const_mul ‖Qt‖
  let err := fun k => ∑ i, m i*(e i k/h k)
  have herr0 : Tendsto err l (𝓝 0) := by
    simpa only [mul_zero,Finset.sum_const_zero,err] using
      tendsto_finsetSum Finset.univ (fun i _ => (he i).const_mul (m i))
  have hlim : Tendsto (fun k => D+e0 k/h k-err k+δ k/2) l (𝓝 D) := by
    simpa using ((he0.const_add D).sub herr0).add (hδ0.div_const 2)
  apply ge_of_tendsto hlim
  filter_upwards [hh,hproj,hcontact,hupper] with k hhk hpk hck huk
  have hform : -δ k*h k ≤ Qt (d k) (d k) := by
    have hq := projected_quadratic_lower S Qt hQ (d k)
    have hP : 0 ≤ ‖S.starProjection (d k)‖ := norm_nonneg _
    have hPN : 0 ≤ Kp*h k := mul_nonneg hKp.le hhk.le
    have hPsq := mul_self_le_mul_self hP hpk
    have hcross := mul_le_mul_of_nonneg_right hpk (norm_nonneg (d k))
    have hb : 2*‖S.starProjection (d k)‖*‖d k‖+‖S.starProjection (d k)‖^2 ≤
        (2*Kp*‖d k‖+Kp^2*h k)*h k := by
      change ‖S.starProjection (d k)‖ ≤ Kp*h k at hpk
      nlinarith only [hPsq,hcross]
    have H := neg_le_neg (mul_le_mul_of_nonneg_left hb (norm_nonneg Qt))
    calc
      -δ k*h k = -(‖Qt‖*((2*Kp*‖d k‖+Kp^2*h k)*h k)) := by dsimp [δ]; ring
      _ ≤ -‖Qt‖*(2*‖S.starProjection (d k)‖*‖d k‖+‖S.starProjection (d k)‖^2) := by
        simpa only [neg_mul] using H
      _ ≤ Qt (d k) (d k) := hq
  have hcancel : ∑ i, m i*inner ℝ (a i) (d k) = 0 := by
    simpa only [sum_inner,real_inner_smul_left,inner_zero_left] using
      congrArg (fun x => inner ℝ x (d k)) hbar
  have hQt : Qt (d k) (d k) = ∑ i, m i*Q i (d k) (d k) := by
    simp only [Qt,sum_apply,smul_apply,smul_eq_mul]
  have havg : h k*(∑ i, m i*B i)+Qt (d k) (d k)/2+∑ i, m i*e i k ≤ U k := by
    have H := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) =>
      mul_le_mul_of_nonneg_left (hck i) (hm i).le)
    have heq : (∑ i, m i*(h k*B i+inner ℝ (a i) (d k)+Q i (d k) (d k)/2+e i k)) =
        h k*(∑ i, m i*B i)+Qt (d k) (d k)/2+∑ i, m i*e i k := by
      calc
        _ = ∑ i, (h k*(m i*B i)+m i*inner ℝ (a i) (d k)+
            (m i*Q i (d k) (d k))/2+m i*e i k) := by
          apply Finset.sum_congr rfl; intro i _; ring
        _ = _ := by
          simp only [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.sum_div,hcancel,add_zero,hQt]
    rw [heq,←Finset.sum_mul,hs,one_mul] at H
    exact H
  have herr : err k*h k = ∑ i, m i*e i k := by
    dsimp only [err]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_assoc,div_mul_cancel₀ _ hhk.ne']
  apply (mul_le_mul_iff_left₀ hhk).mp
  have hrem : h k*(D+e0 k/h k-err k+δ k/2) =
      h k*D+e0 k-∑ i, m i*e i k+δ k*h k/2 := by
    rw [mul_add,mul_sub,mul_add,mul_div_cancel₀ _ hhk.ne',mul_comm (h k) (err k),herr]
    ring
  rw [mul_comm (∑ i, m i * B i) (h k),
    mul_comm (D + e0 k / h k - err k + δ k / 2) (h k), hrem]
  nlinarith only [havg,hform,huk]

end

open Set Filter
open scoped Topology

lemma compact_minimizers_tendsto {M T : Type*} [TopologicalSpace M] [CompactSpace M]
    {l : Filter T} {f : M → ℝ} (hf : Continuous f) {x : M}
    (hmin : ∀ y, f x ≤ f y) (hunique : ∀ y, f y = f x → y = x)
    {u : T → M} (hval : Tendsto (fun k => f (u k)) l (𝓝 (f x))) :
    Tendsto u l (𝓝 x) := by
  rw [tendsto_nhds]
  intro s hs hxs
  by_cases he : sᶜ.Nonempty
  · obtain ⟨y,hy,hym⟩ := hs.isClosed_compl.isCompact.exists_isMinOn he hf.continuousOn
    have hstrict : f x < f y := lt_of_le_of_ne (hmin y) (by
      intro h
      have hyx := hunique y h.symm
      exact hy (hyx ▸ hxs))
    filter_upwards [hval.eventually (gt_mem_nhds hstrict)] with k hk
    by_contra hn
    exact (not_le_of_gt hk) (hym hn)
  · filter_upwards [] with k
    by_contra hn
    exact he ⟨u k,hn⟩

lemma perturbed_compact_minimizers_tendsto {M T : Type*}
    [TopologicalSpace M] [CompactSpace M] {l : Filter T}
    {f : M → ℝ} (hf : Continuous f) {x : M}
    (hmin : ∀ y, f x ≤ f y) (hunique : ∀ y, f y = f x → y = x)
    {u : T → M} {h : T → ℝ} {K : ℝ}
    (hh0 : Tendsto h l (𝓝 0))
    (hbound : ∀ᶠ k in l, f (u k) ≤ f x + K*h k) :
    Tendsto u l (𝓝 x) := by
  apply compact_minimizers_tendsto hf hmin hunique
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa using tendsto_const_nhds.add (tendsto_const_nhds.mul hh0))
    (Eventually.of_forall (fun k => hmin (u k))) hbound

lemma affine_minimum_derivative {M T : Type*}
    [TopologicalSpace M] [CompactSpace M] {l : Filter T}
    {f B : M → ℝ} (hf : Continuous f) (hB : Continuous B) {x : M}
    (hmin : ∀ y, f x ≤ f y) (hunique : ∀ y, f y = f x → y = x)
    {u : T → M} {h : T → ℝ}
    (hh : ∀ᶠ k in l, 0 < h k) (hh0 : Tendsto h l (𝓝 0))
    (hu : ∀ᶠ k in l, ∀ y, f (u k)-h k*B (u k) ≤ f y-h k*B y) :
    Tendsto (fun k => (f (u k)-h k*B (u k)-f x)/h k) l (𝓝 (-B x)) := by
  obtain ⟨K,hK⟩ := (isCompact_univ.image hB).bddAbove
  have hbound : ∀ᶠ k in l, f (u k) ≤ f x+(K-B x)*h k := by
    filter_upwards [hh,hu] with k hhk huk
    have HK := hK (mem_image_of_mem B (mem_univ (u k)))
    have H := huk x
    nlinarith only [H,mul_le_mul_of_nonneg_left HK hhk.le]
  have hconv := perturbed_compact_minimizers_tendsto hf hmin hunique hh0 hbound
  have hlim : Tendsto (fun k => -B (u k)) l (𝓝 (-B x)) :=
    (hB.continuousAt.tendsto.comp hconv).neg
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim tendsto_const_nhds
  · filter_upwards [hh] with k hhk
    apply (le_div_iff₀ hhk).mpr
    have H := hmin (u k)
    nlinarith only [H]
  · filter_upwards [hh,hu] with k hhk huk
    apply (div_le_iff₀ hhk).mpr
    have H := huk x
    nlinarith only [H]

lemma second_remainder_along_sqrt {E T : Type*} [NormedAddCommGroup E]
    {l : Filter T} {R : E → ℝ} {d : T → E} {h : T → ℝ} {K : ℝ}
    (hR : R =o[𝓝 0] (fun v : E => ‖v‖^2))
    (hd0 : Tendsto d l (𝓝 0)) (hh : ∀ᶠ k in l, 0 ≤ h k)
    (hd : ∀ᶠ k in l, ‖d k‖^2 ≤ K*h k) :
    Tendsto (fun k => R (d k)/h k) l (𝓝 0) := by
  have HO : (fun k => ‖d k‖^2) =O[l] h := by
    apply Asymptotics.isBigO_iff.mpr
    refine ⟨K,?_⟩
    filter_upwards [hh,hd] with k hk hd'
    simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (‖d k‖)),abs_of_nonneg hk] using hd'
  exact ((hR.comp_tendsto hd0).trans_isBigO HO).tendsto_div_nhds_zero

end ParameterVariation

open Set Filter Manifold Bundle
open scoped Topology ContDiff

open ParameterVariation

section CompactEnvelopes
variable {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]

def modifiedDatum (v : M → ℝ) (a D b : ℝ) (B : ℝ → ℝ) (y : M) : ℝ :=
  v y+b*B ((v y-a)/D)

def modifiedExcess (v : M → ℝ) (a D b : ℝ) (Bc Bo : ℝ → ℝ) (y : M) : ℝ :=
  modifiedDatum v a D b Bc y-cTransform (cTransform (modifiedDatum v a D b Bo)) y

omit [CompactSpace M] [Nonempty M] in
lemma continuous_modifiedDatum {v : M → ℝ} (hv : Continuous v) (a D b : ℝ)
    {B : ℝ → ℝ} (hB : Continuous B) : Continuous (modifiedDatum v a D b B) :=
  hv.add (continuous_const.mul (hB.comp ((hv.sub continuous_const).div_const D)))

def parameterPenalty (bplus b : ℝ) : ℝ := b/4096+2*b^2/bplus

def regularizedComparison (v : M → ℝ) (a D bplus t : ℝ)
    (Bc Bo : ℝ → ℝ) (q : ℝ×M) : ℝ :=
  hopfLax t (cTransform (modifiedDatum v a D q.1 Bo)) q.2+
    hopfLax (1-t) (modifiedDatum v a D q.1 Bc) q.2-parameterPenalty bplus q.1

lemma modified_outer_decrease_bounds {v : M → ℝ} (hv : Continuous v)
    {a D b h H : ℝ} {B : ℝ → ℝ} (hB : Continuous B)
    (hh : 0 ≤ h) (hbound : ∀ s, 0 ≤ B s ∧ B s ≤ H) (x : M) :
    0 ≤ cTransform (modifiedDatum v a D (b-h) B) x-
      cTransform (modifiedDatum v a D b B) x ∧
    cTransform (modifiedDatum v a D (b-h) B) x-
      cTransform (modifiedDatum v a D b B) x ≤ h*H := by
  have hw := continuous_modifiedDatum hv a D b hB
  have hw' := continuous_modifiedDatum hv a D (b-h) hB
  have H1 := cTransform_antitone hw' hw (fun y => by
    dsimp only [modifiedDatum]
    nlinarith only [mul_nonneg hh (hbound ((v y-a)/D)).1]) x
  have H2 := cTransform_antitone (v := fun y => modifiedDatum v a D b B y + (-h*H))
    (hw.add continuous_const) hw' (fun y => by
    dsimp only [modifiedDatum]
    nlinarith only [mul_le_mul_of_nonneg_left (hbound ((v y-a)/D)).2 hh]) x
  rw [cTransform_add_const hw] at H2
  constructor <;> linarith only [H1,H2]

end CompactEnvelopes

variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.hopfLax_minimizer_unique (hmtw : WeakMTW (n := n) (M := M))
    {v : M → ℝ} (hv : Continuous v) {t : ℝ} (ht : 0<t) (ht1 : t<1)
    {z x y : M}
    (hx : hopfLax t (cTransform v) z=cTransform v x+cost x z/t)
    (hy : hopfLax t (cTransform v) z=cTransform v y+cost y z/t) : x=y := by
  obtain ⟨p,hp,hpz⟩ := exists_minimizing_vector (n := n) x z
  obtain ⟨q,hq,hqz⟩ := exists_minimizing_vector (n := n) y z
  have hpx : t⁻¹ • p∈normalSubdifferential (n := n) (cTransform v) x := by
    apply global_min_divided_cost_subgradient hp ht
    intro w
    rw [hpz,←hx]
    exact hopfLax_le (continuous_cTransform hv) t z w
  have hqy : t⁻¹ • q∈normalSubdifferential (n := n) (cTransform v) y := by
    apply global_min_divided_cost_subgradient hq ht
    intro w
    rw [hqz,←hy]
    exact hopfLax_le (continuous_cTransform hv) t z w
  let X : subgradientGraph (n := n) (cTransform v) := ⟨⟨x,t⁻¹ • p⟩,hpx⟩
  let Y : subgradientGraph (n := n) (cTransform v) := ⟨⟨y,t⁻¹ • q⟩,hqy⟩
  have hXY : graphProjection (cTransform v) t X=graphProjection (cTransform v) t Y := by
    dsimp only [graphProjection,X,Y]
    rw [smul_smul,smul_smul,mul_inv_cancel₀ ht.ne',one_smul,one_smul,hpz,hqz]
  exact congrArg (fun w : subgradientGraph (n := n) (cTransform v) => w.1.1)
    (hmtw.injective_graphProjection hv ht ht1 hXY)

lemma modified_active_split_contact {v : M → ℝ} (hv : Continuous v)
    {a D b h t q : ℝ} {B : ℝ → ℝ} (hB : Continuous B) {x z x' : M}
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hp : p∈minimizingVectors x)
    (hact : contactGap (cTransform (modifiedDatum v a D b B))
      (modifiedDatum v a D b B) x (riemannianExp x p)=0)
    (hq : 0<q) (hq1 : q<1) :
    h*B ((v (riemannianExp x p)-a)/D)+
      (cost x' z-cost x z)/t-
      (cost x' (riemannianExp x (q • p))-cost x (riemannianExp x (q • p)))/q ≤
      (cTransform (modifiedDatum v a D (b-h) B) x'+cost x' z/t)-
      (cTransform (modifiedDatum v a D b B) x+cost x z/t) := by
  have Hg := cTransform_gap_nonneg (continuous_modifiedDatum hv a D (b-h) hB)
    x' (riemannianExp x p)
  have Hs := minimizing_split_upper_support hp hq hq1 x'
  have Hx := minimizing_split_contact hp hq hq1
  dsimp only [contactGap,modifiedDatum] at hact Hg
  simp only [sub_div] at hact Hg Hs Hx ⊢
  nlinarith only [Hg,Hs,Hx,hact]

lemma WeakMTW.modified_pole_movement (hmtw : WeakMTW (n := n) (M := M))
    {v : M → ℝ} (hv : Continuous v) {a D b t H : ℝ}
    {B : ℝ → ℝ} (hB : Continuous B) (hbound : ∀ s, 0 ≤ B s ∧ B s ≤ H)
    {ι : Type*} [Fintype ι] [Nonempty ι] {x : M}
    (p : ι → TangentSpace 𝓘(ℝ,Model n) x) (m : ι → ℝ)
    (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i=1)
    (hmin : ∀ i, p i∈minimizingVectors x)
    (hactive : ∀ i, contactGap (cTransform (modifiedDatum v a D b B))
      (modifiedDatum v a D b B) x (riemannianExp x (p i))=0)
    (ht : 0<t) (ht1 : t<1) :
    let z := riemannianExp x (t • (∑ i, m i • p i))
    hopfLax t (cTransform (modifiedDatum v a D b B)) z =
      cTransform (modifiedDatum v a D b B) x+cost x z/t ∧
    ∃ X : ℝ → M, ∃ d : ℝ → TangentSpace 𝓘(ℝ,Model n) x, ∃ K : ℝ,
      0 ≤ K ∧
      (∀ h, hopfLax t (cTransform (modifiedDatum v a D (b-h) B)) z=
        cTransform (modifiedDatum v a D (b-h) B) (X h)+cost (X h) z/t) ∧
      Tendsto X (𝓝[>] 0) (𝓝 x) ∧ Tendsto d (𝓝[>] 0) (𝓝 0) ∧
      ∀ᶠ h in 𝓝[>] 0, riemannianExp x (d h)=X h ∧ ‖d h‖^2≤K*h := by
  classical
  dsimp only
  let r := ∑ i, m i • p i
  let z := riemannianExp x (t • r)
  let w := modifiedDatum v a D b B
  let g : ℝ → M → ℝ := fun β => cTransform (modifiedDatum v a D β B)
  have hw : Continuous w := continuous_modifiedDatum hv a D b hB
  have hg : ∀ β, Continuous (g β) := fun β =>
    continuous_cTransform (continuous_modifiedDatum hv a D β hB)
  have hAS : range p ⊆ activeLogs (n := n) w x := by
    rintro _ ⟨i,rfl⟩
    exact ⟨hmin i,hactive i⟩
  have hr : r∈convexHull ℝ (range p) :=
    (convex_convexHull ℝ (range p)).sum_mem (fun i _ => (hm i).le) hsum
      (fun i _ => subset_convexHull ℝ (range p) (mem_range_self i))
  have hrsub := active_hull_subset_normalSubdifferential hw x ((convexHull_mono hAS) hr)
  let G : subgradientGraph (n := n) (cTransform w) := ⟨⟨x,r⟩,hrsub⟩
  have hval : hopfLax t (g b) z=g b x+cost x z/t := by
    exact hmtw.hopfLax_graph_value hw ht ht1 G
  refine ⟨hval,?_⟩
  have hID : ∀ q∈convexHull ℝ (range p), t • q∈injectivityDomain x :=
    fun q hq => hmtw.active_hull_precut hw ht ht1 x q ((convexHull_mono hAS) hq)
  obtain ⟨β,hβ,hgrowth⟩ := hmtw.active_local_growth hw p m hm hsum hmin hactive ht ht1 hID
  choose X hX hXmin using (fun h : ℝ => exists_hopfLax_minimizer (hg (b-h)) t z)
  let f : M → ℝ := fun y => g b y+cost y z/t
  have hf : Continuous f := (hg b).add ((continuous_cost_left z).div_const t)
  have hfmin : ∀ y, f x ≤ f y := by
    intro y
    have H := hopfLax_le (hg b) t z y
    rwa [hval] at H
  have hfunique : ∀ y, f y=f x → y=x := by
    intro y hy
    exact hmtw.hopfLax_minimizer_unique hw ht ht1 (hval.trans hy.symm) hval
  have hXbound : ∀ᶠ h : ℝ in 𝓝[>] 0, f (X h)≤f x+H*h := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    have HL := modified_outer_decrease_bounds (a := a) (D := D) (b := b) hv hB (le_of_lt hh) hbound (X h)
    have HR := modified_outer_decrease_bounds (a := a) (D := D) (b := b) hv hB (le_of_lt hh) hbound x
    have HM := hXmin h x
    change g (b-h) (X h)+cost (X h) z/t≤g (b-h) x+cost x z/t at HM
    change 0 ≤ g (b-h) (X h)-g b (X h) ∧ _ at HL
    change 0 ≤ g (b-h) x-g b x ∧ _ at HR
    change g b (X h)+cost (X h) z/t≤g b x+cost x z/t+H*h
    linarith only [HL.1,HR.2,HM]
  have hh0 : Tendsto (fun h : ℝ => h) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_right nhdsWithin_le_nhds
  have hX0 : Tendsto X (𝓝[>] 0) (𝓝 x) :=
    perturbed_compact_minimizers_tendsto hf hfmin hfunique hh0 hXbound
  obtain ⟨L,hL,hLx,hLi⟩ := exists_smooth_fiber_log (zero_mem_injectivityDomain (n := n) x)
  simp only [riemannianExp_zero] at hL hLx hLi
  let d : ℝ → TangentSpace 𝓘(ℝ,Model n) x := fun h => L (X h)
  have hd0 : Tendsto d (𝓝[>] 0) (𝓝 0) := by
    rw [←hLx]
    exact hL.continuousAt.tendsto.comp hX0
  have hdrep : ∀ᶠ h : ℝ in 𝓝[>] 0, riemannianExp x (d h)=X h :=
    hX0.eventually hLi
  have hH : 0 ≤ H := (hbound 0).1.trans (hbound 0).2
  refine ⟨X,d,H/β,div_nonneg hH hβ.le,hX,hX0,hd0,?_⟩
  filter_upwards [hdrep,hd0.eventually hgrowth,hXbound] with h hrep hgr hbo
  refine ⟨hrep,?_⟩
  rw [hrep] at hgr
  change β*‖d h‖^2≤g b (X h)-g b x+(cost (X h) z-cost x z)/t at hgr
  change g b (X h)+cost (X h) z/t≤g b x+cost x z/t+H*h at hbo
  rw [sub_div] at hgr
  apply (mul_le_mul_iff_left₀ hβ).mp
  calc ‖d h‖^2*β ≤ H*h := by nlinarith only [hgr,hbo]
       _ = H/β*h*β := by field_simp

lemma WeakMTW.modified_prefix_weighted_bound (hmtw : WeakMTW (n := n) (M := M))
    {v : M → ℝ} (hv : Continuous v) {a D b t H U : ℝ}
    {B : ℝ → ℝ} (hB : Continuous B) (hbound : ∀ s, 0 ≤ B s ∧ B s ≤ H)
    {ι : Type*} [Fintype ι] [Nonempty ι] {x : M}
    (p : ι → TangentSpace 𝓘(ℝ,Model n) x) (m : ι → ℝ)
    (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i=1)
    (hmin : ∀ i, p i∈minimizingVectors x)
    (hactive : ∀ i, contactGap (cTransform (modifiedDatum v a D b B))
      (modifiedDatum v a D b B) x (riemannianExp x (p i))=0)
    (ht : 0<t) (ht1 : t<1) {e0 : ℝ → ℝ}
    (he0 : Tendsto (fun h => e0 h/h) (𝓝[>] 0) (𝓝 0))
    (hupper : let z := riemannianExp x (t • (∑ i, m i • p i))
      ∀ᶠ h in 𝓝[>] 0,
        hopfLax t (cTransform (modifiedDatum v a D (b-h) B)) z-
        hopfLax t (cTransform (modifiedDatum v a D b B)) z≤h*U+e0 h) :
    ∑ i, m i*B ((v (riemannianExp x (p i))-a)/D) ≤ U := by
  classical
  let E := TangentSpace 𝓘(ℝ,Model n) x
  let : FiniteDimensional ℝ E := inferInstanceAs (FiniteDimensional ℝ (Model n))
  let r := ∑ i, m i • p i
  let z := riemannianExp x (t • r)
  let w := modifiedDatum v a D b B
  have hw : Continuous w := continuous_modifiedDatum hv a D b hB
  have hAS : range p ⊆ activeLogs (n := n) w x := by
    rintro _ ⟨i,rfl⟩
    exact ⟨hmin i,hactive i⟩
  have hr : r∈convexHull ℝ (range p) :=
    (convex_convexHull ℝ (range p)).sum_mem (fun i _ => (hm i).le) hsum
      (fun i _ => subset_convexHull ℝ (range p) (mem_range_self i))
  have hID : ∀ q∈convexHull ℝ (range p), t • q∈injectivityDomain x :=
    fun q hq => hmtw.active_hull_precut hw ht ht1 x q ((convexHull_mono hAS) hq)
  have hrt := hID r hr
  obtain ⟨q,htq,hq1⟩ := exists_between ht1
  have hq : 0<q := ht.trans htq
  have hqi : ∀ i, q • p i∈injectivityDomain x :=
    fun i => contracted_minimizer_mem_injectivityDomain (hmin i) hq hq1
  let f : ι → E → ℝ := fun i d =>
    t⁻¹*(normalCost x (t • r) d-normalCost x (t • r) 0)-
    q⁻¹*(normalCost x (q • p i) d-normalCost x (q • p i) 0)
  let A : ι → E := fun i => p i-r
  let Q : ι → E →L[ℝ] E →L[ℝ] ℝ := fun i => fderiv ℝ (fderiv ℝ (f i)) 0
  have hleft : ContDiffAt ℝ 2 (normalCost x (t • r)) 0 :=
    (normalCost_contDiffAt hrt).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hright : ∀ i, ContDiffAt ℝ 2 (normalCost x (q • p i)) 0 :=
    fun i => (normalCost_contDiffAt (hqi i)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hf : ∀ i, ContDiffAt ℝ 2 (f i) 0 := fun i =>
    (contDiffAt_const.mul (hleft.sub contDiffAt_const)).sub
      (contDiffAt_const.mul ((hright i).sub contDiffAt_const))
  have hf0 : ∀ i, f i 0=0 := fun i => by simp only [f,sub_self,mul_zero]
  have hfirst : ∀ i, fderiv ℝ (f i) 0=innerSL ℝ (A i) := by
    intro i
    have HD := (((normalCost_hasFDerivAt_zero hrt).sub_const
      (normalCost x (t • r) 0)).const_smul t⁻¹).sub
      (((normalCost_hasFDerivAt_zero (hqi i)).sub_const
        (normalCost x (q • p i) 0)).const_smul q⁻¹)
    have HD' : HasFDerivAt (f i) (innerSL ℝ (A i)) 0 := by
      apply HD.congr_fderiv
      ext v
      simp only [A,sub_apply,smul_apply,innerSL_apply_apply,inner_neg_left,
        real_inner_smul_left,inner_sub_left,smul_eq_mul]
      field_simp [ht.ne',hq.ne']
      ring
    exact HD'.fderiv
  have hsecond : ∀ i v, Q i v v=
      hessianValue x (t • r) v/t-hessianValue x (q • p i) v/q := by
    intro i v
    dsimp only [Q,f]
    rw [second_fderiv_scaled_differences hleft (hright i)]
    rw [hessianValue_eq_normalHessian hrt,hessianValue_eq_normalHessian (hqi i)]
    simp only [normalHessian,div_eq_mul_inv]
    ring
  have hbar : ∑ i, m i • A i=0 := by
    simp only [A,smul_sub,Finset.sum_sub_distrib,←Finset.sum_smul,hsum,one_smul,r,sub_self]
  have hQ : ∀ v∈(Submodule.span ℝ (range A))ᗮ, 0 ≤ (∑ i, m i • Q i) v v := by
    intro v hv
    by_cases hv0 : v=0
    · simp [hv0]
    have horth : ∀ i, inner ℝ v (p i-r)=0 := by
      intro i
      rw [real_inner_comm]
      exact (Submodule.mem_orthogonal _ _).mp hv (A i)
        (Submodule.subset_span (mem_range_self i))
    have HS := hmtw.finite_transverse_slack_strict p m hm hsum hmin ht htq hq1 hID hv0 horth
    have HQ : (∑ i, m i • Q i) v v=
        hessianValue x (t • r) v/t-∑ i, m i*(hessianValue x (q • p i) v/q) := by
      simp only [sum_apply,smul_apply,smul_eq_mul,hsecond,mul_sub,Finset.sum_sub_distrib,
        ←Finset.sum_mul,hsum,one_mul]
    rw [HQ]
    exact (sub_pos.mpr HS).le
  obtain ⟨hval,X,d,K,hK,hX,hX0,hd0,hd⟩ :=
    hmtw.modified_pole_movement hv hB hbound p m hm hsum hmin hactive ht ht1
  let V : ℝ → ℝ := fun h => hopfLax t (cTransform (modifiedDatum v a D (b-h) B)) z-
    hopfLax t (cTransform (modifiedDatum v a D b B)) z
  let e : ι → ℝ → ℝ := fun i h => f i (d h)-inner ℝ (A i) (d h)-Q i (d h) (d h)/2
  have HE : ∀ i, Tendsto (fun h => e i h/h) (𝓝[>] 0) (𝓝 0) := by
    intro i
    have HR := contDiffAt_second_order_remainder (hf i)
    simp only [hf0,sub_zero,hfirst,innerSL_apply_apply] at HR
    have Hres := second_remainder_along_sqrt (d := d) (h := fun h : ℝ => h) HR hd0
      (show ∀ᶠ h : ℝ in 𝓝[>] 0, 0 ≤ h from
        (show ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h from self_mem_nhdsWithin).mono (fun _ h => h.le))
      (hd.mono (fun _ h => h.2))
    exact Hres
  have HC : ∀ᶠ h : ℝ in 𝓝[>] 0, ∀ i,
      h*B ((v (riemannianExp x (p i))-a)/D)+inner ℝ (A i) (d h)+
        Q i (d h) (d h)/2+e i h≤V h := by
    filter_upwards [hd] with h hdh i
    have HS := modified_active_split_contact hv hB (hmin i) (hactive i)
      hq hq1 (t := t) (h := h) (z := z) (x' := X h)
    rw [←hX h,←hval] at HS
    change h*B ((v (riemannianExp x (p i))-a)/D)+
      (cost (X h) z-cost x z)/t-
      (cost (X h) (riemannianExp x (q • p i))-cost x (riemannianExp x (q • p i)))/q≤V h at HS
    rw [←hdh.1] at HS
    have HF : f i (d h)=(cost (riemannianExp x (d h)) z-cost x z)/t-
        (cost (riemannianExp x (d h)) (riemannianExp x (q • p i))-
          cost x (riemannianExp x (q • p i)))/q := by
      simp only [f,normalCost,riemannianExp_zero,z,div_eq_mul_inv,mul_comm]
    dsimp only [e]
    rw [HF]
    linarith only [HS]
  exact weighted_parameter_bound (l := 𝓝[>] (0 : ℝ)) (h := fun h : ℝ => h) A (fun i => B ((v (riemannianExp x (p i))-a)/D)) Q
    hm hsum hbar hK (show ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h from self_mem_nhdsWithin)
    (tendsto_id.mono_right nhdsWithin_le_nhds) (hd.mono (fun _ h => h.2)) HE he0 hupper HC hQ

lemma WeakMTW.modified_parameter_inequality
    (hmtw : WeakMTW (n := n) (M := M))
    {v : M → ℝ} (hv : Continuous v) {a D b bplus t H : ℝ}
    {Bc Bo : ℝ → ℝ} (hc : Continuous Bc) (ho : Continuous Bo)
    (hbound : ∀ s, 0 ≤ Bo s ∧ Bo s ≤ H)
    {ι : Type*} [Fintype ι] [Nonempty ι] {x y : M}
    (p : ι → TangentSpace 𝓘(ℝ,Model n) x) (m : ι → ℝ)
    (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i=1)
    (hmin : ∀ i, p i∈minimizingVectors x)
    (hactive : ∀ i, contactGap (cTransform (modifiedDatum v a D b Bo))
      (modifiedDatum v a D b Bo) x (riemannianExp x (p i))=0)
    (ht : 0<t) (ht1 : t<1) (hb : 0≤b) (hbp : 0<bplus)
    (hcenter : let z := riemannianExp x (t • (∑ i, m i • p i))
      ∀ w, hopfLax (1-t) (modifiedDatum v a D b Bc) z =
        modifiedDatum v a D b Bc w+cost w z/(1-t) ↔ w=y)
    (hmax : let z := riemannianExp x (t • (∑ i, m i • p i))
      ∀ᶠ β in 𝓝 b, regularizedComparison v a D bplus t Bc Bo (β,z)≤
        regularizedComparison v a D bplus t Bc Bo (b,z)) :
    1/4096+4*b/bplus ≤ Bc ((v y-a)/D)-∑ i, m i*Bo ((v (riemannianExp x (p i))-a)/D) ∧
      (1:ℝ)/4096 ≤ 1/4096+4*b/bplus := by
  classical
  let z := riemannianExp x (t • (∑ i, m i • p i))
  let C : ℝ → ℝ := fun β => hopfLax (1-t) (modifiedDatum v a D β Bc) z
  let f : M → ℝ := fun w => modifiedDatum v a D b Bc w+cost w z/(1-t)
  let G : M → ℝ := fun w => Bc ((v w-a)/D)
  have hf : Continuous f := (continuous_modifiedDatum hv a D b hc).add
    ((continuous_cost_left z).div_const (1-t))
  have hG : Continuous G := hc.comp ((hv.sub continuous_const).div_const D)
  have hcval : C b=f y := (hcenter y).mpr rfl
  have hfmin : ∀ w, f y≤f w := by
    intro w
    rw [←hcval]
    exact hopfLax_le (continuous_modifiedDatum hv a D b hc) (1-t) z w
  have hfunique : ∀ w, f w=f y → w=y := fun w hw =>
    (hcenter w).mp (hcval.trans hw.symm)
  choose Y hY hYmin using (fun h : ℝ =>
    exists_hopfLax_minimizer (continuous_modifiedDatum hv a D (b-h) hc) (1-t) z)
  have hh : ∀ᶠ h : ℝ in 𝓝[>] 0, 0<h := self_mem_nhdsWithin
  have hh0 : Tendsto (fun h : ℝ => h) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_right nhdsWithin_le_nhds
  have HCY : ∀ᶠ h : ℝ in 𝓝[>] 0, ∀ w, f (Y h)-h*G (Y h)≤f w-h*G w := by
    apply Eventually.of_forall
    intro h w
    have H := hYmin h w
    dsimp only [f,G,modifiedDatum] at H ⊢
    linarith only [H]
  have HC0 : Tendsto (fun h => (C (b-h)-C b)/h) (𝓝[>] 0) (𝓝 (-G y)) := by
    have H := affine_minimum_derivative hf hG hfmin hfunique hh hh0 HCY
    apply H.congr'
    apply Eventually.of_forall
    intro h
    dsimp only [C]
    rw [hY h,show hopfLax (1-t) (modifiedDatum v a D b Bc) z=f y from hcval]
    dsimp only [f,G,modifiedDatum]
    congr 1
    ring
  let dP := (1:ℝ)/4096+4*b/bplus
  have HP0 : Tendsto (fun h => (parameterPenalty bplus (b-h)-parameterPenalty bplus b)/h)
      (𝓝[>] 0) (𝓝 (-dP)) := by
    have H : Tendsto (fun h : ℝ => 2*h/bplus-dP) (𝓝[>] 0) (𝓝 (-dP)) := by
      simpa using ((tendsto_const_nhds.mul hh0).div_const bplus).sub tendsto_const_nhds
    apply H.congr'
    filter_upwards [hh] with h hpos
    dsimp only [parameterPenalty,dP]
    field_simp [hpos.ne',hbp.ne']
    ring
  let U := G y-dP
  let e0 : ℝ → ℝ := fun h => parameterPenalty bplus (b-h)-parameterPenalty bplus b-
    (C (b-h)-C b)-h*U
  have HE0 : Tendsto (fun h => e0 h/h) (𝓝[>] 0) (𝓝 0) := by
    have H := (HP0.sub HC0).sub (tendsto_const_nhds (x := U))
    have H' : Tendsto (fun h =>
        (parameterPenalty bplus (b-h)-parameterPenalty bplus b)/h-
        (C (b-h)-C b)/h-U) (𝓝[>] 0) (𝓝 0) := by
      have hlimit : -dP - -G y - U = 0 := by dsimp only [U]; ring
      simpa only [hlimit] using H
    apply H'.congr'
    filter_upwards [hh] with h hpos
    dsimp only [e0]
    field_simp [hpos.ne']
  have hb0 : Tendsto (fun h : ℝ => b-h) (𝓝[>] 0) (𝓝 b) := by
    simpa using tendsto_const_nhds.sub hh0
  have HU : ∀ᶠ h : ℝ in 𝓝[>] 0,
      hopfLax t (cTransform (modifiedDatum v a D (b-h) Bo)) z-
        hopfLax t (cTransform (modifiedDatum v a D b Bo)) z≤h*U+e0 h := by
    filter_upwards [hb0.eventually hmax] with h hmh
    dsimp only [regularizedComparison] at hmh
    dsimp only [e0,C]
    linarith only [hmh]
  have Hlow := hmtw.modified_prefix_weighted_bound hv ho hbound p m hm hsum hmin hactive ht ht1 HE0 HU
  constructor
  · change dP≤G y-_
    change _≤G y-dP at Hlow
    linarith only [Hlow]
  · have Hpos : 0≤4*b/bplus := div_nonneg (mul_nonneg (by norm_num) hb) hbp.le
    linarith only [Hpos]

end WeakMTWTransport

end

end OAI
