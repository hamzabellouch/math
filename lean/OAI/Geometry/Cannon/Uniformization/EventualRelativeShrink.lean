import Mathlib
import OAI.Geometry.Cannon.Boundary.PolynomialPacking

namespace OAI

section
section
section
section
section
noncomputable section
namespace CannonRealization
open Set Filter Topology Metric

variable {X Y : Type*} [MetricSpace X] [CompactSpace X]
  [MetricSpace Y] [CompactSpace Y]

def EventualRelativeShrink (F : ℕ → C(X,Y)) : Prop :=
  ∀ ε : ℝ, 0<ε → ∃ τ : ℝ, 0<τ ∧ ∀ R : ℝ, 0<R →
    ∀ᶠ n : ℕ in atTop, ∀ x a b : X,
      dist x a ≤ τ*R → R ≤ dist x b →
        dist (F n x) (F n a) ≤ ε*dist (F n x) (F n b)

def RelativeShrink (f : X → Y) : Prop :=
  ∀ ε : ℝ, 0<ε → ∃ τ : ℝ, 0<τ ∧ ∀ x a b : X,
    dist x a ≤ τ*dist x b →
      dist (f x) (f a) ≤ ε*dist (f x) (f b)

omit [CompactSpace X] in
lemma EventualRelativeShrink.equicontinuous {F : ℕ → C(X,Y)}
    (hF : EventualRelativeShrink F) {p q : X} (hpq : p≠q) :
    Equicontinuous (fun n x => F n x) := by
  intro x
  rw [Metric.equicontinuousAt_iff_right]
  intro ε hε
  let B := diam (univ : Set Y)+1
  have hB : 0<B := by dsimp [B]; positivity
  obtain ⟨τ,hτ,hτF⟩ := hF (ε/(2*B)) (by positivity)
  let R := dist p q/2
  have hR : 0<R := half_pos (dist_pos.mpr hpq)
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hτF R hR)
  have hb : ∃ b : X, R≤dist x b := by
    by_cases hp : R≤dist x p
    · exact ⟨p,hp⟩
    · refine ⟨q,?_⟩
      have hh := dist_triangle p x q
      rw [dist_comm p x] at hh
      dsimp [R] at *
      linarith
  obtain ⟨b,hb⟩ := hb
  have hfinite : ∀ᶠ a in 𝓝 x, ∀ n ∈ Finset.range N, dist (F n x) (F n a)<ε := by
    apply (eventually_all_finset _).mpr
    intro n _
    simpa only [mem_ball,dist_comm] using
      (F n).continuous.continuousAt.eventually (ball_mem_nhds (F n x) hε)
  filter_upwards [hfinite,ball_mem_nhds x (mul_pos hτ hR)] with a ha hnear n
  by_cases hn : n<N
  · exact ha n (by simpa using hn)
  · have hsmall : dist x a≤τ*R := by simpa only [mem_ball,dist_comm] using (mem_ball.mp hnear).le
    have hh := hN n (le_of_not_gt hn) x a b hsmall hb
    have hdist : dist (F n x) (F n b)≤B :=
      (dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ _) (mem_univ _)).trans (by dsimp [B]; linarith)
    have hh' := mul_le_mul_of_nonneg_left hdist (show 0≤ε/(2*B) by positivity)
    have he : (ε/(2*B))*B=ε/2 := by field_simp
    rw [he] at hh'
    exact (hh.trans hh').trans_lt (half_lt_self hε)

lemma compact_map_subsequence (F : ℕ → C(X,Y))
    (heq : Equicontinuous (fun n x => F n x)) :
    ∃ f : C(X,Y), ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (F ∘ φ) atTop (𝓝 f) := by
  classical
  have : T2Space (UniformOnFun X Y {K | IsCompact K}) :=
    UniformOnFun.t2Space_of_covering (by
      apply eq_univ_of_forall
      intro x
      exact mem_sUnion_of_mem (mem_singleton x) isCompact_singleton)
  have hc : IsCompact (closure (range F)) := by
    apply ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
      (F := fun g : C(X,Y) => (g : X → Y)) (𝔖 := {K | IsCompact K}) (fun _ h => h)
    · exact ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isClosedEmbedding
    · intro K _
      have hindex : ∀ g : range F, ∃ n, F n=g.val := fun g => g.property
      choose index hindex using hindex
      have heq' := heq.comp index
      have heq'' : Equicontinuous (fun g : range F => (g.val : X → Y)) := by
        convert heq' using 1
        funext g x
        exact congrArg (fun h : C(X,Y) => h x) (hindex g).symm
      exact heq''.equicontinuousOn K
    · intro K _ x _
      exact ⟨univ,isCompact_univ,subset_univ _⟩
  obtain ⟨f,_,φ,hφ,ht⟩ := hc.tendsto_subseq (fun n => subset_closure (mem_range_self n))
  exact ⟨f,φ,hφ,ht⟩

omit [CompactSpace X] [CompactSpace Y] in
lemma EventualRelativeShrink.limit {F : ℕ → C(X,Y)} (hF : EventualRelativeShrink F)
    {f : C(X,Y)} {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (ht : Tendsto (F ∘ φ) atTop (𝓝 f)) : RelativeShrink f := by
  intro ε hε
  obtain ⟨τ,hτ,hbound⟩ := hF ε hε
  refine ⟨τ,hτ,?_⟩
  intro x a b hdist
  by_cases hb : x=b
  · subst b
    have ha : x=a := dist_le_zero.mp (by simpa using hdist)
    simp [←ha]
  · have heval (z : X) : Tendsto (fun n => F (φ n) z) atTop (𝓝 (f z)) :=
      (continuous_eval_const z).tendsto f |>.comp ht
    apply le_of_tendsto_of_tendsto ((heval x).dist (heval a))
      (((heval x).dist (heval b)).const_mul ε)
    exact (hφ.tendsto_atTop.eventually (hbound (dist x b) (dist_pos.mpr hb))).mono
      (fun n hn => hn x a b hdist le_rfl)

omit [CompactSpace X] [CompactSpace Y] in
theorem RelativeShrink.injective [PreconnectedSpace X] {f : C(X,Y)}
    (hf : RelativeShrink f) {p q : X} (hpq : f p≠f q) : Function.Injective f := by
  intro x y hxy
  by_contra hne
  let S : Set X := {z | f z=f x}
  have hxS : x∈S := rfl
  have hyS : y∈S := hxy.symm
  have hSc : IsClosed S := isClosed_eq f.continuous continuous_const
  obtain ⟨τ,hτ,hbound⟩ := hf 1 zero_lt_one
  have hSo : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    have hw : ∃ w : X, w∈S ∧ z≠w := by
      by_cases hzx : z=x
      · exact ⟨y,hyS,by simpa [hzx] using hne⟩
      · exact ⟨x,hxS,hzx⟩
    obtain ⟨w,hw,hzw⟩ := hw
    apply mem_of_superset (ball_mem_nhds z (mul_pos hτ (dist_pos.mpr hzw)))
    intro a ha
    have hh := hbound z a w (by simpa only [mem_ball,dist_comm] using (mem_ball.mp ha).le)
    have hzw' : f z=f w := hz.trans hw.symm
    rw [hzw',dist_self,mul_zero] at hh
    have he : f w=f a := dist_le_zero.mp hh
    exact he.symm.trans hw
  have hSu : S=univ := IsClopen.eq_univ ⟨hSc,hSo⟩ ⟨x,hxS⟩
  have hp : p∈S := hSu ▸ mem_univ p
  have hq : q∈S := hSu ▸ mem_univ q
  exact hpq (hp.trans hq.symm)

omit [CompactSpace Y] in
lemma surjective_limit {F : ℕ → C(X,Y)} (hF : ∀ n, Function.Surjective (F n))
    {f : C(X,Y)} {φ : ℕ → ℕ} (ht : Tendsto (F ∘ φ) atTop (𝓝 f)) :
    Function.Surjective f := by
  intro y
  choose x hx using fun n => hF (φ n) y
  obtain ⟨z,_,ψ,hψ,hz⟩ := isCompact_univ.tendsto_subseq (fun n => mem_univ (x n))
  have ht' := ht.comp hψ.tendsto_atTop
  have he := continuous_eval.tendsto (f,z) |>.comp (ht'.prodMk_nhds hz)
  have hy : Tendsto (fun _ : ℕ => y) atTop (𝓝 (f z)) := by
    simpa only [Function.comp_def,hx] using he
  exact ⟨z,tendsto_nhds_unique hy tendsto_const_nhds⟩

theorem realization_homeomorph_limit [PreconnectedSpace X]
    (F : ℕ → C(X,Y)) (hsurj : ∀ n, Function.Surjective (F n))
    (hshrink : EventualRelativeShrink F)
    {p q : X} {u v : Y} (huv : u≠v)
    (hp : ∀ n, F n p=u) (hq : ∀ n, F n q=v) :
    ∃ f : X ≃ₜ Y, RelativeShrink f ∧ ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (F ∘ φ) atTop (𝓝 (⟨f,f.continuous⟩ : C(X,Y))) := by
  have hpq : p≠q := fun h => huv ((hp 0).symm.trans ((congrArg (F 0) h).trans (hq 0)))
  obtain ⟨f,φ,hφ,ht⟩ := compact_map_subsequence F (hshrink.equicontinuous hpq)
  have hf := hshrink.limit hφ ht
  have hfp : f p=u := by
    have he := (continuous_eval_const p).tendsto f |>.comp ht
    have he' : Tendsto (fun _ : ℕ => u) atTop (𝓝 (f p)) := by simpa [Function.comp_def,hp] using he
    exact tendsto_nhds_unique he' tendsto_const_nhds
  have hfq : f q=v := by
    have he := (continuous_eval_const q).tendsto f |>.comp ht
    have he' : Tendsto (fun _ : ℕ => v) atTop (𝓝 (f q)) := by simpa [Function.comp_def,hq] using he
    exact tendsto_nhds_unique he' tendsto_const_nhds
  have hn : f p≠f q := by rwa [hfp,hfq]
  let H := (Equiv.ofBijective f ⟨hf.injective hn,surjective_limit hsurj ht⟩).toHomeomorphOfContinuousClosed
    f.continuous f.continuous.isClosedMap
  exact ⟨H,hf,φ,hφ,ht⟩

end CannonRealization

end
end
section
noncomputable section
open Set Metric

namespace CannonRealization
open Set Metric

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

def WeakQS (f : X → Y) (H : ℝ) : Prop :=
  ∀ x a b, dist x a ≤ dist x b → dist (f x) (f a) ≤ H*dist (f x) (f b)

lemma radial_point [PreconnectedSpace Y] (u v : Y) {r : ℝ}
    (hr : 0≤r) (hrv : r≤dist u v) : ∃ w : Y, dist u w=r := by
  have hh := isPreconnected_univ.intermediate_value (mem_univ u) (mem_univ v)
    ((continuous_const.dist continuous_id).continuousOn : ContinuousOn (fun w : Y => dist u w) univ)
  obtain ⟨w,_,hw⟩ := hh (by simpa only [id_eq,dist_self,mem_Icc] using And.intro hr hrv)
  exact ⟨w,hw⟩

theorem inverse_weakQS_ratio_bound [PreconnectedSpace Y]
    (f : X ≃ₜ Y) {Q : ℕ} {C H : ℝ}
    (hpack : CannonPacking.PolynomialPacking (X:=X) Q C) (hC : 0≤C)
    (hdiam : ∀ x y : X, dist x y≤1) (hH : 1≤H)
    (hf : WeakQS f.symm H) {t : ℝ} (ht : 1≤t) :
    ∃ K : ℝ, 0<K ∧ ∀ x a b : X, dist x a≤t*dist x b →
      dist (f x) (f a)≤K*dist (f x) (f b) := by
  classical
  have hHp : 0<H := zero_lt_one.trans_le hH
  have htp : 0<t := zero_lt_one.trans_le ht
  obtain ⟨N,hN⟩ := exists_nat_ge (C*(H^3*t)^Q)
  refine ⟨(2:ℝ)^N,pow_pos (by norm_num) _,?_⟩
  intro x a b hab
  by_cases hxb : x=b
  · subst b
    have hxa : x=a := dist_le_zero.mp (by simpa only [dist_self,mul_zero] using hab)
    simp [←hxa]
  have hR : 0<dist x b := dist_pos.mpr hxb
  have hB : 0<dist (f x) (f b) := dist_pos.mpr (fun hh => hxb (f.injective hh))
  by_contra hn
  have hlarge : (2:ℝ)^N*dist (f x) (f b) ≤ dist (f x) (f a) := (lt_of_not_ge hn).le
  have hpoints (i : Fin (N+1)) : ∃ z : Y, dist (f x) z=(2:ℝ)^i.val*dist (f x) (f b) := by
    apply radial_point (f x) (f a) (by positivity)
    exact (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2)
      (Nat.le_of_lt_succ i.isLt)) hB.le).trans hlarge
  choose z hz using hpoints
  let p (i : Fin (N+1)) : X := f.symm (z i)
  let R := dist x b
  let r := min (H*t*R) 1
  let s := R/H^2
  have hs : 0<s := div_pos hR (sq_pos_of_pos hHp)
  have hH2 : 1≤H^2 := one_le_pow₀ hH
  have hsR : s≤R := by
    apply (div_le_iff₀ (sq_pos_of_pos hHp)).mpr
    exact le_mul_of_one_le_right hR.le hH2
  have hRHt : R≤H*t*R := by
    exact le_mul_of_one_le_left hR.le (one_le_mul_of_one_le_of_one_le hH ht)
  have hsr : s≤r := le_min (hsR.trans hRHt) (hsR.trans (hdiam x b))
  have hball (i : Fin (N+1)) : dist x (p i)≤r := by
    have htop : dist (f x) (z i)≤dist (f x) (f a) := by
      rw [hz]
      exact (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2)
        (Nat.le_of_lt_succ i.isLt)) hB.le).trans hlarge
    have hh := hf (f x) (z i) (f a) htop
    simp only [f.symm_apply_apply] at hh
    have hh' : dist x (p i)≤H*t*R := by
      exact hh.trans (by dsimp [R]; nlinarith [mul_le_mul_of_nonneg_left hab hHp.le])
    exact le_min hh' (hdiam x (p i))
  have hlower (i : Fin (N+1)) : R≤H*dist x (p i) := by
    have hh := hf (f x) (f b) (z i) (by
      rw [hz]
      exact le_mul_of_one_le_left hB.le (one_le_pow₀ (by norm_num)))
    simpa only [f.symm_apply_apply] using hh
  have hsep_le (i j : Fin (N+1)) (hij : i.val<j.val) : s≤dist (p i) (p j) := by
    have hpow : 2*((2:ℝ)^i.val) ≤ (2:ℝ)^j.val := by
      rw [mul_comm,←pow_succ]
      exact pow_le_pow_right₀ (by norm_num) (Nat.succ_le_of_lt hij)
    have hzi : dist (z i) (f x)≤dist (z i) (z j) := by
      have hh := dist_triangle (f x) (z i) (z j)
      rw [hz i,hz j] at hh
      rw [dist_comm, hz i]
      nlinarith [mul_le_mul_of_nonneg_right hpow hB.le]
    have hh := hf (z i) (f x) (z j) hzi
    simp only [f.symm_apply_apply] at hh
    change dist (p i) x≤H*dist (p i) (p j) at hh
    rw [dist_comm (p i) x] at hh
    apply (div_le_iff₀ (sq_pos_of_pos hHp)).mpr
    have hl := hlower i
    nlinarith [mul_le_mul_of_nonneg_left hh hHp.le]
  have hsep (i j : Fin (N+1)) (hij : i≠j) : s≤dist (p i) (p j) := by
    rcases lt_or_gt_of_ne (fun hh => hij (Fin.ext hh)) with hh|hh
    · exact hsep_le i j hh
    · simpa only [dist_comm] using hsep_le j i hh
  have hh := CannonPacking.indexed_packing Q C hpack p Finset.univ x r s hs hsr
    (min_le_right _ _) (fun i _ => hball i) (fun i _ j _ hij => hsep i j hij)
  have hratio : r/s≤H^3*t := by
    apply (div_le_iff₀ hs).mpr
    have he : H^3*t*s=H*t*R := by dsimp [s]; field_simp
    rw [he]
    exact min_le_left _ _
  have htotal : (N+1:ℕ)≤C*(H^3*t)^Q := by
    simpa only [Finset.card_univ,Fintype.card_fin] using
      hh.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (div_nonneg (hs.le.trans hsr) hs.le) hratio Q) hC)
  have hhN : (N:ℝ)+1≤C*(H^3*t)^Q := by exact_mod_cast htotal
  linarith

end CannonRealization

end
end
noncomputable section
namespace CannonRealization
open Set Metric

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

theorem RelativeShrink.inverse_weakQS (f : X ≃ₜ Y) (hf : RelativeShrink f) :
    ∃ H : ℝ, 1≤H ∧ WeakQS f.symm H := by
  obtain ⟨τ,hτ,hbound⟩ := hf (1/2) (by norm_num)
  refine ⟨max 1 τ⁻¹,le_max_left _ _,?_⟩
  intro x a b hab
  by_cases ha : x=a
  · subst a
    simp only [dist_self]
    positivity
  have hA : 0<dist x a := dist_pos.mpr ha
  have hh : τ*dist (f.symm x) (f.symm a)≤dist (f.symm x) (f.symm b) := by
    by_contra! hn
    have hz := hbound (f.symm x) (f.symm b) (f.symm a) hn.le
    simp only [f.apply_symm_apply] at hz
    linarith
  have hh' : dist (f.symm x) (f.symm a)≤τ⁻¹*dist (f.symm x) (f.symm b) := by
    have hz := (le_div_iff₀ hτ).mpr (show dist (f.symm x) (f.symm a)*τ≤dist (f.symm x) (f.symm b) by nlinarith [hh])
    simpa only [div_eq_mul_inv,mul_comm] using hz
  exact hh'.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) dist_nonneg)

theorem RelativeShrink.forward_ratio_bounds [PreconnectedSpace Y]
    (f : X ≃ₜ Y) (hf : RelativeShrink f) {Q : ℕ} {C : ℝ}
    (hpack : CannonPacking.PolynomialPacking (X:=X) Q C) (hC : 0≤C)
    (hdiam : ∀ x y : X, dist x y≤1) :
    ∀ t : ℝ, 1≤t → ∃ K : ℝ, 0<K ∧ ∀ x a b : X,
      dist x a≤t*dist x b → dist (f x) (f a)≤K*dist (f x) (f b) := by
  obtain ⟨H,hH,hInv⟩ := hf.inverse_weakQS f
  intro t ht
  exact inverse_weakQS_ratio_bound f hpack hC hdiam hH hInv ht

theorem RelativeShrink.forward_weakQS [PreconnectedSpace Y]
    (f : X ≃ₜ Y) (hf : RelativeShrink f) {Q : ℕ} {C : ℝ}
    (hpack : CannonPacking.PolynomialPacking (X:=X) Q C) (hC : 0≤C)
    (hdiam : ∀ x y : X, dist x y≤1) :
    ∃ H : ℝ, 1≤H ∧ WeakQS f H := by
  obtain ⟨K,hK,hbound⟩ := hf.forward_ratio_bounds f hpack hC hdiam 1 le_rfl
  refine ⟨max 1 K,le_max_left _ _,?_⟩
  intro x a b hab
  exact (hbound x a b (by simpa only [one_mul] using hab)).trans
    (mul_le_mul_of_nonneg_right (le_max_right _ _) dist_nonneg)

end CannonRealization

namespace CannonRealization
open Set Metric

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

lemma small_scale_geometric [PreconnectedSpace X] {f : X → Y} {H τ : ℝ}
    (_hH : 0≤H) (hf : WeakQS f H) (hτ : 0<τ) (hτ1 : τ≤1)
    (hc : ∀ x a b, dist x a≤τ*dist x b →
      dist (f x) (f a)≤(1/2:ℝ)*dist (f x) (f b))
    (n : ℕ) (x a b : X) (ha : dist x a≤τ^n*dist x b) :
    dist (f x) (f a)≤H*(1/2:ℝ)^n*dist (f x) (f b) := by
  induction n generalizing a with
  | zero => simpa only [pow_zero,mul_one,one_mul] using hf x a b (by simpa using ha)
  | succ n ih =>
    obtain ⟨c,hcR⟩ := radial_point x b (show 0≤τ^n*dist x b by positivity)
      (mul_le_of_le_one_left dist_nonneg (pow_le_one₀ hτ.le hτ1))
    have hh := hc x a c (by rw [hcR]; simpa only [pow_succ,mul_assoc,mul_left_comm,mul_comm] using ha)
    have hh' := ih c hcR.le
    rw [pow_succ]
    nlinarith

lemma large_scale_geometric [PreconnectedSpace X] {f : X → Y} {K : ℝ}
    (hK : 0≤K)
    (hf : ∀ x a b, dist x a≤2*dist x b → dist (f x) (f a)≤K*dist (f x) (f b))
    (n : ℕ) (x a b : X) (ha : dist x a≤(2:ℝ)^n*dist x b) :
    dist (f x) (f a)≤K^(n+1)*dist (f x) (f b) := by
  induction n generalizing a with
  | zero =>
    simpa only [zero_add,pow_one] using hf x a b (by simp only [pow_zero,one_mul] at ha; nlinarith [dist_nonneg (x:=x) (y:=b)])
  | succ n ih =>
    obtain ⟨c,hc⟩ := radial_point x a (show 0≤dist x a/2 by positivity) (by nlinarith [dist_nonneg (x:=x) (y:=a)])
    have h1 := hf x a c (by rw [hc]; linarith)
    have h2 := ih c (by rw [hc]; rw [pow_succ] at ha; nlinarith)
    have h3 := mul_le_mul_of_nonneg_left h2 hK
    rw [pow_succ K (n+1)]
    nlinarith

theorem relative_small_power [PreconnectedSpace X] {f : X → Y} {H : ℝ}
    (hH : 0<H) (hf : WeakQS f H) (hshrink : RelativeShrink f) :
    ∃ α : ℝ, 0<α ∧ α≤1 ∧ ∀ t : ℝ, 0<t → t≤1 → ∀ x a b : X,
      dist x a≤t*dist x b →
      dist (f x) (f a)≤2*H*t^α*dist (f x) (f b) := by
  obtain ⟨τ,hτ,hc⟩ := hshrink (1/2) (by norm_num)
  obtain ⟨k,hk⟩ := exists_pow_lt_of_lt_one (lt_min hτ (by norm_num : (0:ℝ)<1)) (by norm_num : (1/2:ℝ)<1)
  have hk0 : k≠0 := by intro h; subst k; norm_num at hk
  have hkpos : 0<k := Nat.pos_of_ne_zero hk0
  let σ : ℝ := (1/2:ℝ)^k
  have hσ : 0<σ := pow_pos (by norm_num) _
  have hστ : σ≤τ := hk.le.trans (min_le_left _ _)
  have hσ1 : σ<1 := hk.trans_le (min_le_right _ _)
  have hak : 0<(k:ℝ) := by exact_mod_cast hkpos
  have ha : 0<(k:ℝ)⁻¹ := inv_pos.mpr hak
  refine ⟨(k:ℝ)⁻¹,ha,?_,?_⟩
  · apply inv_le_one_of_one_le₀
    exact_mod_cast hkpos
  · intro t ht ht1 x a b hab
    obtain ⟨n,hnlow,hnup⟩ := exists_nat_pow_near_of_lt_one ht ht1 hσ hσ1
    have hgeom := small_scale_geometric hH.le hf hσ hσ1.le (fun x a b hh =>
      hc x a b (hh.trans (mul_le_mul_of_nonneg_right hστ dist_nonneg))) n x a b
      (hab.trans (mul_le_mul_of_nonneg_right hnup dist_nonneg))
    have hid : σ^(k:ℝ)⁻¹=(1/2:ℝ) := Real.pow_rpow_inv_natCast (by norm_num) hk0
    have hp : (1/2:ℝ)^(n+1)≤t^(k:ℝ)⁻¹ := by
      have hh := Real.rpow_le_rpow (pow_nonneg hσ.le _) hnlow.le ha.le
      rw [←Real.rpow_pow_comm hσ.le,hid] at hh
      exact hh
    have hp' : (1/2:ℝ)^n≤2*t^(k:ℝ)⁻¹ := by rw [pow_succ] at hp; linarith
    exact hgeom.trans (by nlinarith [mul_le_mul_of_nonneg_left hp' (mul_nonneg hH.le (dist_nonneg (x:=f x) (y:=f b)))])

theorem relative_large_power [PreconnectedSpace X] {f : X → Y} {K : ℝ}
    (hK : 0<K)
    (hf : ∀ x a b, dist x a≤2*dist x b → dist (f x) (f a)≤K*dist (f x) (f b)) :
    ∃ β : ℕ, 0<β ∧ ∀ t : ℝ, 1≤t → ∀ x a b : X,
      dist x a≤t*dist x b →
      dist (f x) (f a)≤K^2*t^β*dist (f x) (f b) := by
  obtain ⟨k,hk⟩ := pow_unbounded_of_one_lt (max K 1) (by norm_num : (1:ℝ)<2)
  have hk0 : 0<k := by
    by_contra! h
    have hz : k=0 := Nat.eq_zero_of_le_zero h
    rw [hz,pow_zero] at hk
    exact (not_lt_of_ge (le_max_right K 1)) hk
  have hkK : K≤(2:ℝ)^k := (le_max_left _ _).trans hk.le
  refine ⟨k,hk0,?_⟩
  intro t ht x a b hab
  obtain ⟨n,hnlow,hnup⟩ := exists_nat_pow_near ht (by norm_num : (1:ℝ)<2)
  have hgeom := large_scale_geometric hK.le hf (n+1) x a b
    (hab.trans (mul_le_mul_of_nonneg_right hnup.le dist_nonneg))
  have hpow : K^n≤t^k := by
    calc
      _ ≤ ((2:ℝ)^k)^n := pow_le_pow_left₀ hK.le hkK _
      _ = ((2:ℝ)^n)^k := by rw [←pow_mul,←pow_mul,Nat.mul_comm]
      _ ≤ t^k := pow_le_pow_left₀ (by positivity) hnlow _
  have hbound := mul_le_mul_of_nonneg_left hpow (sq_nonneg K)
  have he : K^(n+1+1)=K^2*K^n := by rw [show n+1+1=2+n by omega,pow_add]
  rw [he] at hgeom
  exact hgeom.trans (by nlinarith [mul_le_mul_of_nonneg_right hbound (dist_nonneg (x:=f x) (y:=f b))])

end CannonRealization

end
end
section
noncomputable section
namespace CannonDistortion
open Set
open scoped NNReal

def maxIso {A B : Type*} [LinearOrder A] [LinearOrder B]
    (f g : A ≃o B) : A ≃o B :=
  StrictMono.orderIsoOfSurjective (fun x => max (f x) (g x))
    (fun a b hab => max_lt_iff.mpr ⟨(f.strictMono hab).trans_le (le_max_left _ _),
      (g.strictMono hab).trans_le (le_max_right _ _)⟩) (by
    intro y
    rcases le_total (f.symm y) (g.symm y) with h|h
    · refine ⟨f.symm y,?_⟩
      change max (f (f.symm y)) (g (f.symm y))=y
      rw [f.apply_symm_apply]
      exact max_eq_left ((g.monotone h).trans_eq (g.apply_symm_apply y))
    · refine ⟨g.symm y,?_⟩
      change max (f (g.symm y)) (g (g.symm y))=y
      rw [g.apply_symm_apply]
      exact max_eq_right ((f.monotone h).trans_eq (f.apply_symm_apply y)))

@[simp] lemma maxIso_apply {A B : Type*} [LinearOrder A] [LinearOrder B]
    (f g : A ≃o B) (x : A) : maxIso f g x=max (f x) (g x) := rfl

def powerGauge (α β t : ℝ) : ℝ := max (t^α) (t^β)

def powerIso (C : ℝ≥0) (hC : 0<C) (α β : ℝ) (hα : 0<α) (hβ : 0<β) : ℝ≥0 ≃o ℝ≥0 :=
  (maxIso (NNReal.orderIsoRpow α hα) (NNReal.orderIsoRpow β hβ)).trans (OrderIso.mulLeft₀ C hC)

lemma powerIso_coe (C : ℝ≥0) (hC : 0<C) (α β : ℝ) (hα : 0<α) (hβ : 0<β) (t : ℝ≥0) :
    ((powerIso C hC α β hα hβ t : ℝ≥0) : ℝ)=(C:ℝ)*powerGauge α β t := by
  rfl

lemma powerGauge_nonneg {α β t : ℝ} (ht : 0 ≤ t) : 0 ≤ powerGauge α β t :=
  (Real.rpow_nonneg ht α).trans (le_max_left _ _)

lemma powerGauge_monotone {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) : powerGauge α β s ≤ powerGauge α β t :=
  max_le_max (Real.rpow_le_rpow hs hst hα) (Real.rpow_le_rpow hs hst hβ)

theorem mixed_power_bound {α β r : ℝ} (_hα : 0<α) (_hβ : 0<β) (hab : α ≤ β) (hr : 0<r) :
    powerGauge α β (Real.sqrt r)*powerGauge α β (5*max r 1)  ≤
      (5:ℝ)^β*powerGauge (α/2) (3*β/2) r := by
  have hs : 0<Real.sqrt r := Real.sqrt_pos.mpr hr
  have hbig : 1 ≤ 5*max r 1 := by nlinarith [le_max_right r 1]
  have hgb : powerGauge α β (5*max r 1)=(5*max r 1)^β :=
    max_eq_right (Real.rpow_le_rpow_of_exponent_le hbig hab)
  rw [hgb]
  rcases le_total r 1 with hr1|h1r
  · have hs1 : Real.sqrt r ≤ 1 := Real.sqrt_le_one.mpr hr1
    have hgs : powerGauge α β (Real.sqrt r)=(Real.sqrt r)^α :=
      max_eq_left (Real.rpow_le_rpow_of_exponent_ge hs hs1 hab)
    rw [hgs,max_eq_right hr1,mul_one]
    have he : (Real.sqrt r)^α=r^(α/2) := by
      rw [Real.sqrt_eq_rpow,←Real.rpow_mul hr.le]
      congr 1
      ring
    rw [he,mul_comm]
    exact mul_le_mul_of_nonneg_left (le_max_left _ _) (Real.rpow_nonneg (by norm_num) β)
  · have hs1 : 1 ≤ Real.sqrt r := Real.one_le_sqrt.mpr h1r
    have hgs : powerGauge α β (Real.sqrt r)=(Real.sqrt r)^β :=
      max_eq_right (Real.rpow_le_rpow_of_exponent_le hs1 hab)
    rw [hgs,max_eq_left h1r,Real.mul_rpow (by norm_num : (0:ℝ) ≤ 5) hr.le]
    have he : (Real.sqrt r)^β*(5^β*r^β)=5^β*r^(3*β/2) := by
      rw [Real.sqrt_eq_rpow,←Real.rpow_mul hr.le]
      calc
        _ = 5^β*(r^((1/2:ℝ)*β)*r^β) := by ring
        _ = 5^β*r^((1/2:ℝ)*β+β) := by rw [Real.rpow_add hr]
        _ = _ := by congr 2; ring
    rw [he]
    exact mul_le_mul_of_nonneg_left (le_max_right _ _) (Real.rpow_nonneg (by norm_num) β)

end CannonDistortion

end
end
namespace CannonRealization
open CannonDistortion Metric

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

theorem RelativeShrink.power_control [PreconnectedSpace X] [PreconnectedSpace Y]
    (f : X ≃ₜ Y) (hf : RelativeShrink f) {Q : ℕ} {P : ℝ}
    (hpack : CannonPacking.PolynomialPacking (X:=X) Q P) (hP : 0 ≤ P)
    (hdiam : ∀ x y : X, dist x y ≤ 1) :
    ∃ C α β : ℝ, 0<C ∧ 0<α ∧ α ≤ β ∧ 0<β ∧ ∀ t : ℝ, 0 ≤ t → ∀ x a b : X,
      dist x a ≤ t*dist x b →
      dist (f x) (f a) ≤ C*powerGauge α β t*dist (f x) (f b) := by
  obtain ⟨H,hH,hweak⟩ := hf.forward_weakQS f hpack hP hdiam
  have hHp : 0<H := zero_lt_one.trans_le hH
  obtain ⟨α,hα,hα1,hsmall⟩ := relative_small_power hHp hweak hf
  obtain ⟨K,hK,hKbound⟩ := hf.forward_ratio_bounds f hpack hP hdiam 2 (by norm_num)
  obtain ⟨β,hβ,hlarge⟩ := relative_large_power hK hKbound
  have hβ1 : (1:ℝ) ≤ (β:ℝ) := by exact_mod_cast hβ
  let C := max (2*H) (K^2)
  have hC : 0<C := (mul_pos (by norm_num) hHp).trans_le (le_max_left _ _)
  refine ⟨C,α,(β:ℝ),hC,hα,hα1.trans hβ1,zero_lt_one.trans_le hβ1,?_⟩
  intro t ht x a b hab
  by_cases ht0 : t=0
  · subst t
    have hxa : x=a := dist_le_zero.mp (by simpa only [zero_mul] using hab)
    rw [←hxa,dist_self]
    exact mul_nonneg (mul_nonneg hC.le (powerGauge_nonneg (by norm_num))) dist_nonneg
  have htp : 0<t := lt_of_le_of_ne ht (Ne.symm ht0)
  rcases le_total t 1 with ht1|h1t
  · have hh := hsmall t htp ht1 x a b hab
    apply hh.trans
    have hleft : 2*H*t^α ≤ C*powerGauge α (β:ℝ) t :=
      mul_le_mul (le_max_left _ _) (le_max_left _ _) (Real.rpow_nonneg ht _) hC.le
    exact mul_le_mul_of_nonneg_right hleft dist_nonneg
  · have hh := hlarge t h1t x a b hab
    apply hh.trans
    have hright : K^2*t^β ≤ C*powerGauge α (β:ℝ) t := by
      rw [←Real.rpow_natCast t β]
      exact mul_le_mul (le_max_right _ _) (le_max_right _ _) (Real.rpow_nonneg ht _) hC.le
    exact mul_le_mul_of_nonneg_right hright dist_nonneg

end CannonRealization

end
end
end

end OAI
