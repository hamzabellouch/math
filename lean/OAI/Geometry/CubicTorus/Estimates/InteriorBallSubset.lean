import Mathlib
import OAI.Geometry.CubicTorus.Estimates.L2ReplacementBallBound

namespace OAI

section
section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma interior_ball_subset {R s : ℝ} {x : Plane}
    (hR : 0<R) (hx : x∈Metric.ball (0 : Plane) (R/4)) (hs : s≤R/4) :
    Metric.ball x s⊆Metric.ball 0 R := by
  intro y hy
  have hh := dist_triangle y x (0 : Plane)
  have hy' : dist y x<s := hy
  have hx' : dist x 0<R/4 := hx
  change dist y 0<R
  linarith

theorem cmc_uniform_energy {p : Plane → Plane} (hp : Continuous p)
    (hpb : ∀ y,‖p y‖≤1) {R α D β : ℝ} (hR : 0<R) (hα : 0<α) (hD : 0≤D)
    (hβ : 0<β) (hβ2 : β<2)
    (hHolder : ∀ x∈Metric.ball (0 : Plane) R,∀ y∈Metric.ball (0 : Plane) R,
      ‖cmcJacobian (p x)-cmcJacobian (p y)‖≤D*(dist x y)^α)
    (u : Lp ℝ 2 (volume : Measure Plane)) (G : Lp Plane 2 (volume : Measure Plane))
    (hg : PlaneWeakGradient (Metric.ball 0 R) u G)
    (hd : ∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆Metric.ball 0 R → (∫ y,fderiv ℝ ψ y (cmcJacobian (p y) (G y)))=0) :
    ∃ S K : ℝ,0<S ∧ S≤1 ∧ S≤R/4 ∧ 0≤K ∧ D*S^α≤1 ∧
      ∀ x∈Metric.ball (0 : Plane) (R/4),∀ s : ℝ,0<s → s≤S →
        (∫ y in Metric.ball x s,‖G y‖^2)≤K*s^β := by
  obtain ⟨C,δ₀,hC,hδ,hδ1,hdecay⟩ := cmc_energy_decay_at hβ hβ2
  obtain ⟨S,hS,hSbound,hSsmall⟩ := exists_small_power_scale hα hδ
    (lt_min zero_lt_one (by positivity : 0<R/4)) D
  have hS1 : S≤1 := hSbound.trans (min_le_left _ _)
  have hSR : S≤R/4 := hSbound.trans (min_le_right _ _)
  refine ⟨S,C/S^β*‖G‖^2,hS,hS1,hSR,by positivity,hSsmall.trans hδ1,?_⟩
  intro x hx s hs hsS
  have hsub := interior_ball_subset hR hx hSR
  have hxR : x∈Metric.ball (0 : Plane) R :=
    (Metric.ball_subset_ball (by linarith : R/4≤R)) hx
  have hosc : ∀ y∈Metric.ball x S,‖cmcJacobian (p x)-cmcJacobian (p y)‖≤δ₀ := by
    intro y hy
    calc
      _ ≤ D*(dist x y)^α := hHolder x hxR y (hsub hy)
      _ ≤ D*S^α := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow dist_nonneg (by simpa only [dist_comm] using (le_of_lt hy : dist y x≤S)) hα.le) hD
      _ ≤ δ₀ := hSsmall
  have hh := hdecay p hp hpb (p x) (hpb x) x S hS hosc u G (hg.mono hsub)
    (fun ψ hψ hc hsp ↦ hd ψ hψ hc (hsp.trans hsub)) s hs hsS
  rw [Real.div_rpow hs.le hS.le] at hh
  convert hh using 1
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem forced_cmc_uniform_energy {p : Plane → Plane} (hp : Continuous p)
    (hpb : ∀ y,‖p y‖≤1) {R α D L β : ℝ} (hR : 0<R) (hα : 0<α)
    (hD : 0≤D) (hL : 0≤L) (hβ : 0<β) (hβ2 : β<2)
    (hHolder : ∀ x∈Metric.ball (0 : Plane) R,∀ y∈Metric.ball (0 : Plane) R,
      ‖cmcJacobian (p x)-cmcJacobian (p y)‖≤D*(dist x y)^α)
    (u : Lp ℝ 2 (volume : Measure Plane)) (G : Lp Plane 2 (volume : Measure Plane))
    {B : Plane → Plane} (hB : Continuous B)
    (hBH : ∀ x∈Metric.ball (0 : Plane) R,∀ y∈Metric.ball (0 : Plane) R,
      ‖B x-B y‖≤L*(dist x y)^α)
    (hg : PlaneWeakGradient (Metric.ball 0 R) u G)
    (hd : ∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆Metric.ball 0 R → (∫ y,fderiv ℝ ψ y (cmcJacobian (p y) (G y)-B y))=0) :
    ∃ S K : ℝ,0<S ∧ S≤1 ∧ S≤R/4 ∧ 0≤K ∧ D*S^α≤1 ∧
      ∀ x∈Metric.ball (0 : Plane) (R/4),∀ s : ℝ,0<s → s≤S →
        (∫ y in Metric.ball x s,‖G y‖^2)≤K*s^β := by
  obtain ⟨A,hA,hreplace⟩ := forced_cmc_replacement_decay_at
  obtain ⟨θ,δ₀,hθ,hθs,hδ,hδ1,hcontract⟩ := exists_decay_contraction (by positivity : 0<2*A+1) hβ hβ2
  have hq : 0<θ^β := Real.rpow_pos_of_pos hθ _
  have hctr := hcontract δ₀ hδ.le le_rfl
  have hctr₁ : A*(8*θ)^2+256*(δ₀/2)^2≤θ^β/2 := by nlinarith [sq_nonneg θ]
  have hctr₂ : θ^2≤θ^β/2 := by nlinarith [sq_nonneg δ₀,mul_nonneg hA.le (sq_nonneg θ)]
  obtain ⟨S,hS,hSbound,hSsmall⟩ := exists_small_power_scale hα (by positivity : 0<δ₀/2)
    (lt_min zero_lt_one (by positivity : 0<R/4)) D
  have hS1 : S≤1 := hSbound.trans (min_le_left _ _)
  have hSR : S≤R/4 := hSbound.trans (min_le_right _ _)
  let M : ℝ := 2*((A+256)*Real.pi*L^2)/(θ^β)
  have hM : 0≤M := by dsimp [M]; positivity
  have hMeq : (A+256)*Real.pi*L^2=θ^β*M/2 := by dsimp [M]; field_simp
  let K : ℝ := θ^(-β)/S^β*(‖G‖^2+M*S^2)
  refine ⟨S,K,hS,hS1,hSR,by dsimp [K]; positivity,hSsmall.trans (by linarith),?_⟩
  intro x hx r hr hrS
  have hxR : x∈Metric.ball (0 : Plane) R :=
    (Metric.ball_subset_ball (by linarith : R/4≤R)) hx
  let E : ℝ → ℝ := fun s ↦ (∫ y in Metric.ball x s,‖G y‖^2)+M*s^2
  have hmono : MonotoneOn E (Ioc 0 S) := by
    intro s hs t ht hst
    apply add_le_add (setIntegral_mono_set (L2_vector_norm_sq_integrable G).integrableOn
      (Eventually.of_forall fun _ ↦ sq_nonneg _) (Metric.ball_subset_ball hst).eventuallyLE)
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs.1.le hst 2) hM
  have hdecay : ∀ s : ℝ,0<s → s≤S → E (θ*s)≤θ^β*E s := by
    intro s hs hsS
    have h8 : 8*(s/8)=s := by ring
    have hsub : Metric.ball x (8*(s/8))⊆Metric.ball 0 R := by
      rw [h8]; exact interior_ball_subset hR hx (hsS.trans hSR)
    have hosc : ∀ y∈Metric.ball x (8*(s/8)),‖cmcJacobian (p x)-cmcJacobian (p y)‖≤δ₀/2 := by
      intro y hy
      apply (hHolder x hxR y (hsub hy)).trans
      apply le_trans _ hSsmall
      apply mul_le_mul_of_nonneg_left _ hD
      apply Real.rpow_le_rpow dist_nonneg _ hα.le
      rw [h8] at hy
      have hxy : dist x y≤ s := by simpa only [dist_comm] using (le_of_lt hy : dist y x≤ s)
      exact hxy.trans hsS
    have hBo : ∀ y∈Metric.ball x (8*(s/8)),‖B y-B x‖≤L := by
      intro y hy
      apply (hBH y (hsub hy) x hxR).trans
      have hy1 : dist y x≤1 := by rw [h8] at hy; exact (le_of_lt hy).trans (hsS.trans hS1)
      have hh := Real.rpow_le_rpow dist_nonneg hy1 hα.le
      rw [Real.one_rpow] at hh
      exact mul_le_of_le_one_right hL hh
    obtain ⟨q,hq'⟩ := hreplace p hp hpb (p x) (hpb x) x (s/8) (δ₀/2) L
      (by positivity) (by positivity) (by linarith) hL hosc u G B hB (B x) hBo (hg.mono hsub)
      (fun ψ hψ hc hs' ↦ hd ψ hψ hc (hs'.trans hsub))
    have hh := (hq' (θ*s) (by positivity) (by nlinarith)).1
    rw [h8,show θ*s/(s/8)=8*θ by field_simp] at hh
    have he : 0≤∫ y in Metric.ball x s,‖G y‖^2 := integral_nonneg (fun _ ↦ sq_nonneg _)
    have hfirst := mul_le_mul_of_nonneg_right hctr₁ he
    have hsecond := mul_le_mul_of_nonneg_right hctr₂ (mul_nonneg hM (sq_nonneg s))
    dsimp [E]
    nlinarith [mul_nonneg hq.le he,show (A+256)*Real.pi*s^2*L^2=θ^β*M/2*s^2 by rw [← hMeq]; ring]
  have hER : E S≤‖G‖^2+M*S^2 := by
    apply add_le_add _ le_rfl
    rw [L2_vector_norm_sq_integral]
    exact setIntegral_le_integral (L2_vector_norm_sq_integrable G) (Eventually.of_forall fun _ ↦ sq_nonneg _)
  have hh := geometric_energy_decay hS (by dsimp [E]; positivity) hθ (by linarith) hβ.le hmono hdecay hr hrS
  have hh' := hh.trans (mul_le_mul_of_nonneg_left hER (by positivity))
  rw [Real.div_rpow hr.le hS.le] at hh'
  have hleft : (∫ y in Metric.ball x r,‖G y‖^2)≤E r := by
    exact le_add_of_nonneg_right (mul_nonneg hM (sq_nonneg r))
  calc
    _ ≤ θ^(-β)*(r^β/S^β)*(‖G‖^2+M*S^2) := hleft.trans hh'
    _ = K*r^β := by dsimp only [K]; ring

end CubicTorus

end
end

section

noncomputable section
open Set Filter
open scoped Topology
namespace CubicTorus

lemma optimized_oscillation_scale {α s : ℝ} (hα : 0<α) (hα1 : α≤1)
    (hs : 0<s) (hs1 : s≤1) :
    0<s^(1+α/2)/16 ∧ s^(1+α/2)/16 ≤ s/8/2 := by
  have hlower : s^(3/2 : ℝ) ≤ s^(1+α/2) :=
    Real.rpow_le_rpow_of_exponent_ge hs hs1 (by linarith)
  have hh := Real.rpow_le_rpow_of_exponent_ge hs hs1 (by linarith : (1:ℝ)≤1+α/2)
  rw [Real.rpow_one] at hh
  exact ⟨div_pos ((Real.rpow_pos_of_pos hs _).trans_le hlower) (by norm_num),by linarith⟩

lemma optimized_oscillation_identity {α s : ℝ} (hα : 0<α) (hs : 0<s)
    (A D K : ℝ) :
    (A*((s^(1+α/2)/16)/(s/8))^4+128*(D*s^α)^2)*(K*s^(2-α/2))=
      ((A/16+128*D^2)*K*16^(2+α/(2+α)))*(s^(1+α/2)/16)^(2+α/(2+α)) := by
  have hr : (s^(1+α/2)/16)/(s/8)=s^(α/2)/2 := by
    rw [Real.rpow_add hs,Real.rpow_one]
    field_simp
    norm_num
  have h4 : (s^(α/2))^4=s^(2*α) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hs.le]
    congr 1
    ring
  have h2 : (s^α)^2=s^(2*α) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hs.le]
    congr 1
    ring
  have he : s^(2*α)*s^(2-α/2)=s^(2+3*α/2) := by
    rw [← Real.rpow_add hs]
    congr 1
    ring
  have hex : (1+α/2)*(2+α/(2+α))=2+3*α/2 := by
    field_simp
    ring
  have hright : 16^(2+α/(2+α))*(s^(1+α/2)/16)^(2+α/(2+α))=s^(2+3*α/2) := by
    rw [← Real.mul_rpow (by norm_num) (by positivity)]
    rw [show (16:ℝ)*(s^(1+α/2)/16)=s^(1+α/2) by ring]
    rw [← Real.rpow_mul hs.le,hex]
  rw [hr,div_pow,mul_pow,h4,h2]
  calc
    _ = (A/16+128*D^2)*K*(s^(2*α)*s^(2-α/2)) := by ring
    _ = (A/16+128*D^2)*K*s^(2+3*α/2) := by rw [he]
    _ = _ := by rw [← hright]; ring

end CubicTorus

end
end

section

noncomputable section
namespace CubicTorus

lemma optimized_power_identity {α s : ℝ} (hα : 0<α) (hs : 0<s) :
    16^(2+α/(2+α))*(s^(1+α/2)/16)^(2+α/(2+α))=s^(2+3*α/2) := by
  have hex : (1+α/2)*(2+α/(2+α))=2+3*α/2 := by field_simp; ring
  rw [← Real.mul_rpow (by norm_num) (by positivity)]
  rw [show (16:ℝ)*(s^(1+α/2)/16)=s^(1+α/2) by ring]
  rw [← Real.rpow_mul hs.le,hex]

lemma forced_optimized_oscillation_bound {α s : ℝ} (hα : 0<α) (hs : 0<s) (hs1 : s≤1)
    (A D K L : ℝ) (hA : 0≤A) :
    (A*((s^(1+α/2)/16)/(s/8))^4+256*(D*s^α)^2)*(K*s^(2-α/2))+
      (A+256)*Real.pi*s^2*(L*s^α)^2 ≤
      (((A/16+256*D^2)*K+(A+256)*Real.pi*L^2)*16^(2+α/(2+α)))*
        (s^(1+α/2)/16)^(2+α/(2+α)) := by
  have hm : (A*((s^(1+α/2)/16)/(s/8))^4+256*(D*s^α)^2)*(K*s^(2-α/2))=
      ((A/16+256*D^2)*K*16^(2+α/(2+α)))*(s^(1+α/2)/16)^(2+α/(2+α)) := by
    convert optimized_oscillation_identity hα hs (A/2) D (2*K) using 1 <;> ring
  have hpower : s^2*(s^α)^2=s^(2+2*α) := by
    rw [← Real.rpow_natCast (s^α) 2,← Real.rpow_mul hs.le,← Real.rpow_natCast s 2,← Real.rpow_add hs]
    congr 1; ring
  have hsmall : s^(2+2*α)≤ s^(2+3*α/2) :=
    Real.rpow_le_rpow_of_exponent_ge hs hs1 (by linarith)
  have hsource : (A+256)*Real.pi*s^2*(L*s^α)^2≤
      (A+256)*Real.pi*L^2*(16^(2+α/(2+α))*(s^(1+α/2)/16)^(2+α/(2+α))) := by
    rw [optimized_power_identity hα hs]
    calc
      _ = (A+256)*Real.pi*L^2*(s^2*(s^α)^2) := by ring
      _ ≤ _ := by rw [hpower]; exact mul_le_mul_of_nonneg_left hsmall (by positivity)
  rw [hm]
  calc
    _ ≤ ((A/16+256*D^2)*K*16^(2+α/(2+α)))*(s^(1+α/2)/16)^(2+α/(2+α))+
        (A+256)*Real.pi*L^2*(16^(2+α/(2+α))*(s^(1+α/2)/16)^(2+α/(2+α))) :=
      add_le_add le_rfl hsource
    _ = _ := by ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem forced_cmc_uniform_oscillation {p : Plane → Plane} (hp : Continuous p)
    (hpb : ∀ y,‖p y‖≤1) {R α D L : ℝ} (hR : 0<R) (hα : 0<α) (hα1 : α≤1) (hD : 0≤D) (hL : 0≤L)
    (hHolder : ∀ x∈Metric.ball (0 : Plane) R,∀ y∈Metric.ball (0 : Plane) R,
      ‖cmcJacobian (p x)-cmcJacobian (p y)‖≤D*(dist x y)^α)
    (u : Lp ℝ 2 (volume : Measure Plane)) (G : Lp Plane 2 (volume : Measure Plane))
    {B : Plane → Plane} (hB : Continuous B)
    (hBH : ∀ x∈Metric.ball (0 : Plane) R,∀ y∈Metric.ball (0 : Plane) R,
      ‖B x-B y‖≤L*(dist x y)^α)
    (hg : PlaneWeakGradient (Metric.ball 0 R) u G)
    (hd : ∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆Metric.ball 0 R → (∫ y,fderiv ℝ ψ y (cmcJacobian (p y) (G y)-B y))=0) :
    ∃ r C γ : ℝ,0<r ∧ 0≤C ∧ 0<γ ∧ γ≤1 ∧
      ∀ x∈Metric.ball (0 : Plane) (R/4),∀ ρ : ℝ,0<ρ → ρ≤r →
        ∃ q : Plane,(∫ y in Metric.ball x ρ,‖G y-q‖^2)≤C*ρ^(2+γ) := by
  obtain ⟨S,K,hS,hS1,hSR,hK,hSsmall,henergy⟩ :=
    forced_cmc_uniform_energy hp hpb hR hα hD hL (by linarith : 0<2-α/2) (by linarith : 2-α/2<2)
      hHolder u G hB hBH hg hd
  obtain ⟨A,hA,hreplace⟩ := forced_cmc_replacement_decay_at
  let k : ℝ := 1+α/2
  have hk : 0<k := by dsimp [k]; linarith
  let γ : ℝ := α/(2+α)
  have hγ : 0<γ := by dsimp [γ]; positivity
  have hγ1 : γ≤1 := (div_le_one (by linarith : 0<2+α)).mpr (by linarith)
  let C : ℝ := ((A/16+256*D^2)*K+(A+256)*Real.pi*L^2)*16^(2+γ)
  refine ⟨S^k/16,C,γ,by positivity,by dsimp [C]; positivity,hγ,hγ1,?_⟩
  intro x hx ρ hρ hρr
  let s : ℝ := (16*ρ)^(1/k)
  have hs : 0<s := Real.rpow_pos_of_pos (by positivity) _
  have hspow : s^k=16*ρ := by
    dsimp [s]
    rw [← Real.rpow_mul (by positivity)]
    rw [one_div_mul_cancel hk.ne',Real.rpow_one]
  have hSpow : (S^k)^(1/k)=S := by
    rw [← Real.rpow_mul hS.le]
    rw [mul_one_div_cancel hk.ne',Real.rpow_one]
  have hsS : s≤S := by
    rw [← hSpow]
    exact Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
  have hs1 : s≤1 := hsS.trans hS1
  have hρeq : s^(1+α/2)/16=ρ := by change s^k/16=ρ; rw [hspow]; ring
  have h8 : 8*(s/8)=s := by ring
  have hsub : Metric.ball x (8*(s/8))⊆Metric.ball 0 R := by
    rw [h8]
    exact interior_ball_subset hR hx (hsS.trans hSR)
  have hxR : x∈Metric.ball (0 : Plane) R :=
    (Metric.ball_subset_ball (by linarith : R/4≤R)) hx
  have hδ1 : D*s^α≤1 :=
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hs.le hsS hα.le) hD).trans hSsmall
  have hosc : ∀ y∈Metric.ball x (8*(s/8)),
      ‖cmcJacobian (p x)-cmcJacobian (p y)‖≤D*s^α := by
    intro y hy
    apply (hHolder x hxR y (hsub hy)).trans
    apply mul_le_mul_of_nonneg_left _ hD
    apply Real.rpow_le_rpow dist_nonneg _ hα.le
    rw [h8] at hy
    exact (dist_comm x y ▸ (le_of_lt hy : dist y x≤ s))
  have hBo : ∀ y∈Metric.ball x (8*(s/8)),‖B y-B x‖≤L*s^α := by
    intro y hy
    apply (hBH y (hsub hy) x hxR).trans
    apply mul_le_mul_of_nonneg_left _ hL
    apply Real.rpow_le_rpow dist_nonneg _ hα.le
    rw [h8] at hy
    exact le_of_lt hy
  obtain ⟨q,hq⟩ := hreplace p hp hpb (p x) (hpb x) x (s/8) (D*s^α) (L*s^α)
    (by positivity) (by positivity) hδ1 (by positivity) hosc u G B hB (B x) hBo (hg.mono hsub)
    (fun ψ hψ hc hs' ↦ hd ψ hψ hc (hs'.trans hsub))
  have hscale := optimized_oscillation_scale hα hα1 hs hs1
  have hh := (hq (s^(1+α/2)/16) hscale.1.le hscale.2).2
  rw [h8,hρeq] at hh
  refine ⟨q,hh.trans ?_⟩
  calc
    _ ≤ (A*(ρ/(s/8))^4+256*(D*s^α)^2)*(K*s^(2-α/2))+
        (A+256)*Real.pi*s^2*(L*s^α)^2 :=
      add_le_add (mul_le_mul_of_nonneg_left (henergy x hx s hs hsS) (by positivity)) le_rfl
    _ ≤ C*ρ^(2+γ) := by
      rw [← hρeq]
      exact forced_optimized_oscillation_bound hα hs hs1 A D K L hA.le

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem cmc_uniform_oscillation {p : Plane → Plane} (hp : Continuous p)
    (hpb : ∀ y,‖p y‖≤1) {R α D : ℝ} (hR : 0<R) (hα : 0<α) (hα1 : α≤1) (hD : 0≤D)
    (hHolder : ∀ x∈Metric.ball (0 : Plane) R,∀ y∈Metric.ball (0 : Plane) R,
      ‖cmcJacobian (p x)-cmcJacobian (p y)‖≤D*(dist x y)^α)
    (u : Lp ℝ 2 (volume : Measure Plane)) (G : Lp Plane 2 (volume : Measure Plane))
    (hg : PlaneWeakGradient (Metric.ball 0 R) u G)
    (hd : ∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆Metric.ball 0 R → (∫ y,fderiv ℝ ψ y (cmcJacobian (p y) (G y)))=0) :
    ∃ r C γ : ℝ,0<r ∧ 0≤C ∧ 0<γ ∧ γ≤1 ∧
      ∀ x∈Metric.ball (0 : Plane) (R/4),∀ ρ : ℝ,0<ρ → ρ≤r →
        ∃ q : Plane,(∫ y in Metric.ball x ρ,‖G y-q‖^2)≤C*ρ^(2+γ) := by
  obtain ⟨S,K,hS,hS1,hSR,hK,hSsmall,henergy⟩ :=
    cmc_uniform_energy hp hpb hR hα hD (by linarith : 0<2-α/2) (by linarith : 2-α/2<2)
      hHolder u G hg hd
  obtain ⟨A,hA,hreplace⟩ := cmc_replacement_decay_at
  let k : ℝ := 1+α/2
  have hk : 0<k := by dsimp [k]; linarith
  let γ : ℝ := α/(2+α)
  have hγ : 0<γ := by dsimp [γ]; positivity
  have hγ1 : γ≤1 := (div_le_one (by linarith : 0<2+α)).mpr (by linarith)
  let C : ℝ := (A/16+128*D^2)*K*16^(2+γ)
  refine ⟨S^k/16,C,γ,by positivity,by dsimp [C]; positivity,hγ,hγ1,?_⟩
  intro x hx ρ hρ hρr
  let s : ℝ := (16*ρ)^(1/k)
  have hs : 0<s := Real.rpow_pos_of_pos (by positivity) _
  have hspow : s^k=16*ρ := by
    dsimp [s]
    rw [← Real.rpow_mul (by positivity)]
    rw [one_div_mul_cancel hk.ne',Real.rpow_one]
  have hSpow : (S^k)^(1/k)=S := by
    rw [← Real.rpow_mul hS.le]
    rw [mul_one_div_cancel hk.ne',Real.rpow_one]
  have hsS : s≤S := by
    rw [← hSpow]
    exact Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
  have hs1 : s≤1 := hsS.trans hS1
  have hρeq : s^(1+α/2)/16=ρ := by change s^k/16=ρ; rw [hspow]; ring
  have h8 : 8*(s/8)=s := by ring
  have hsub : Metric.ball x (8*(s/8))⊆Metric.ball 0 R := by
    rw [h8]
    exact interior_ball_subset hR hx (hsS.trans hSR)
  have hxR : x∈Metric.ball (0 : Plane) R :=
    (Metric.ball_subset_ball (by linarith : R/4≤R)) hx
  have hδ1 : D*s^α≤1 :=
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hs.le hsS hα.le) hD).trans hSsmall
  have hosc : ∀ y∈Metric.ball x (8*(s/8)),
      ‖cmcJacobian (p x)-cmcJacobian (p y)‖≤D*s^α := by
    intro y hy
    apply (hHolder x hxR y (hsub hy)).trans
    apply mul_le_mul_of_nonneg_left _ hD
    apply Real.rpow_le_rpow dist_nonneg _ hα.le
    rw [h8] at hy
    exact (dist_comm x y ▸ (le_of_lt hy : dist y x≤ s))
  obtain ⟨q,hq⟩ := hreplace p hp hpb (p x) (hpb x) x (s/8) (D*s^α)
    (by positivity) (by positivity) hδ1 hosc u G (hg.mono hsub)
    (fun ψ hψ hc hs' ↦ hd ψ hψ hc (hs'.trans hsub))
  have hscale := optimized_oscillation_scale hα hα1 hs hs1
  have hh := (hq (s^(1+α/2)/16) hscale.1.le hscale.2).2
  rw [h8,hρeq] at hh
  refine ⟨q,hh.trans ?_⟩
  calc
    _ ≤ (A*(ρ/(s/8))^4+128*(D*s^α)^2)*(K*s^(2-α/2)) :=
      mul_le_mul_of_nonneg_left (henergy x hx s hs hsS) (by positivity)
    _ = C*ρ^(2+γ) := by
      rw [← hρeq]
      exact optimized_oscillation_identity hα hs A D K

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma plane_ball_real_at (a : Plane) {r : ℝ} (hr : 0≤r) :
    (volume : Measure Plane).real (Metric.ball a r)=Real.pi*r^2 := by
  rw [show volume.real (Metric.ball a r)=volume.real (Metric.ball (0 : Plane) r) by
    simp only [Measure.real,Measure.addHaar_ball_center volume a]]
  exact plane_ball_real hr

lemma plane_L2_sub_const_integrable_at (G : Lp Plane 2 (volume : Measure Plane))
    (q a : Plane) (r : ℝ) : IntegrableOn (fun y ↦ ‖G y-q‖^2) (Metric.ball a r) := by
  let : IsFiniteMeasure (volume.restrict (Metric.ball a r)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hh := ((Lp.memLp G).restrict (Metric.ball a r)).sub (memLp_const q)
  exact (memLp_two_iff_integrable_sq hh.norm.aestronglyMeasurable).mp hh.norm

lemma plane_L2_sub_const_mono (G : Lp Plane 2 (volume : Measure Plane))
    (q : Plane) {a b : Plane} {r s : ℝ} (hsub : Metric.ball a r⊆Metric.ball b s) :
    (∫ y in Metric.ball a r,‖G y-q‖^2)≤(∫ y in Metric.ball b s,‖G y-q‖^2) :=
  setIntegral_mono_set (plane_L2_sub_const_integrable_at G q b s)
    (Eventually.of_forall fun _ ↦ sq_nonneg _) hsub.eventuallyLE

lemma campanato_constant_distance (G : Lp Plane 2 (volume : Measure Plane))
    {a q q' : Plane} {r C β : ℝ} (hr : 0<r) (hC : 0≤C)
    (h₁ : (∫ y in Metric.ball a (r/2),‖G y-q‖^2)≤C*r^(2+2*β))
    (h₂ : (∫ y in Metric.ball a (r/2),‖G y-q'‖^2)≤C*r^(2+2*β)) :
    dist q q'≤4*Real.sqrt C*r^β := by
  have hi := plane_L2_sub_const_integrable_at G q a (r/2)
  have hj := plane_L2_sub_const_integrable_at G q' a (r/2)
  have hc : IntegrableOn (fun _ : Plane ↦ ‖q-q'‖^2) (Metric.ball a (r/2)) :=
    integrableOn_const measure_ball_lt_top.ne
  have hp (y : Plane) : ‖q-q'‖^2≤2*‖G y-q‖^2+2*‖G y-q'‖^2 := by
    have hn : ‖q-q'‖≤‖G y-q‖+‖G y-q'‖ := by
      simpa only [← dist_eq_norm,dist_comm q (G y)] using dist_triangle q (G y) q'
    nlinarith [norm_nonneg (q-q'),norm_nonneg (G y-q),norm_nonneg (G y-q'),
      sq_nonneg (‖G y-q‖-‖G y-q'‖)]
  have hh := integral_mono hc ((hi.const_mul 2).add (hj.const_mul 2)) hp
  change (∫ x in Metric.ball a (r/2),‖q-q'‖^2)≤
    (∫ x in Metric.ball a (r/2),2*‖G x-q‖^2+2*‖G x-q'‖^2) at hh
  rw [integral_add (hi.const_mul 2) (hj.const_mul 2),integral_const_mul,integral_const_mul,
    integral_const,smul_eq_mul] at hh
  rw [show (volume.restrict (Metric.ball a (r/2))).real univ=
    volume.real (Metric.ball a (r/2)) by simp [Measure.real],plane_ball_real_at a (by positivity)] at hh
  have hpow : r^(2+2*β)=r^2*(r^β)^2 := by
    rw [Real.rpow_add hr,Real.rpow_two,mul_comm (2:ℝ) β,Real.rpow_mul hr.le,Real.rpow_two]
  rw [hpow] at h₁ h₂
  have hpi : r^2*‖q-q'‖^2≤Real.pi*r^2*‖q-q'‖^2 := by
    have hπ : (1:ℝ)≤Real.pi := by linarith [Real.pi_gt_three]
    simpa only [one_mul,mul_assoc] using mul_le_mul_of_nonneg_right hπ
      (mul_nonneg (sq_nonneg r) (sq_nonneg ‖q-q'‖))
  have hsquare : ‖q-q'‖^2≤(4*Real.sqrt C*r^β)^2 := by
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hr)).mp
    calc
      _ ≤ 16*C*r^2*(r^β)^2 := by nlinarith
      _ = _ := by rw [mul_pow,mul_pow,Real.sq_sqrt hC]; ring
  rw [dist_eq_norm]
  have hb : 0≤4*Real.sqrt C*r^β := by positivity
  nlinarith [norm_nonneg (q-q')]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma campanato_point_limit (G : Lp Plane 2 (volume : Measure Plane))
    (a : Plane) {R C β : ℝ} (hR : 0<R) (hC : 0≤C) (hβ : 0<β)
    (hosc : ∀ r : ℝ,0<r → r≤R → ∃ q : Plane,
      (∫ y in Metric.ball a r,‖G y-q‖^2)≤C*r^(2+2*β)) :
    ∃ H : Plane,∀ r : ℝ,0<r → r≤R → ∀ q : Plane,
      (∫ y in Metric.ball a r,‖G y-q‖^2)≤C*r^(2+2*β) →
      dist H q≤(4*Real.sqrt C*(1+1/(1-(1/2:ℝ)^β))*2^β)*r^β := by
  let s : ℕ → ℝ := fun i ↦ (1/2:ℝ)^i*R
  have hs (i : ℕ) : 0<s i := by dsimp [s]; positivity
  have hsR (i : ℕ) : s i≤R := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (pow_le_one₀ (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)≤1)) hR.le
  have hsucc (i : ℕ) : s (i+1)=s i/2 := by dsimp [s]; rw [pow_succ]; ring
  choose q hq using fun i ↦ hosc (s i) (hs i) (hsR i)
  let θ : ℝ := (1/2:ℝ)^β
  let M : ℝ := 4*Real.sqrt C
  have hM : 0≤M := by dsimp [M]; positivity
  have hθ : 0<θ := Real.rpow_pos_of_pos (by norm_num) _
  have hθ1 : θ<1 := Real.rpow_lt_one (by norm_num) (by norm_num) hβ
  have hp (i : ℕ) : (s i)^β=R^β*θ^i := by
    dsimp [s,θ]
    rw [Real.mul_rpow (by positivity) hR.le]
    rw [← Real.rpow_natCast_mul (by norm_num : (0:ℝ)≤1/2),mul_comm (i:ℝ),
      Real.rpow_mul (by norm_num : (0:ℝ)≤1/2),Real.rpow_natCast]
    ring
  have hstep (i : ℕ) : dist (q i) (q (i+1))≤(M*R^β)*θ^i := by
    have hlo : s i/2 ≤ s i := by linarith [hs i]
    have h₁ : (∫ y in Metric.ball a (s i/2),‖G y-q i‖^2)≤C*(s i)^(2+2*β) :=
      (plane_L2_sub_const_mono G (q i) (Metric.ball_subset_ball hlo)).trans (hq i)
    have h₂ : (∫ y in Metric.ball a (s i/2),‖G y-q (i+1)‖^2)≤C*(s i)^(2+2*β) := by
      rw [← hsucc]
      apply (hq (i+1)).trans
      apply mul_le_mul_of_nonneg_left _ hC
      exact Real.rpow_le_rpow (hs _).le (by rw [hsucc]; exact hlo) (by linarith)
    have hh := campanato_constant_distance G (hs i) hC h₁ h₂
    rw [hp i] at hh
    exact hh.trans_eq (by dsimp [M]; ring)
  obtain ⟨H,hH⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_of_le_geometric θ (M*R^β) hθ1 hstep)
  have happrox (i : ℕ) : dist H (q i)≤M/(1-θ)*(s i)^β := by
    have hh := dist_le_of_le_geometric_of_tendsto θ (M*R^β) hθ1 hstep hH i
    rw [dist_comm,hp i]
    exact hh.trans_eq (by ring)
  refine ⟨H,fun r hr hrR q₀ hq₀ ↦ ?_⟩
  obtain ⟨i,hi,h'i⟩ := exists_nat_pow_near_of_lt_one (div_pos hr hR)
    ((div_le_one hR).mpr hrR) (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<1)
  have hrsi : r≤ s i := (div_le_iff₀ hR).mp h'i
  have hsir : s i≤2*r := by
    have hh := (lt_div_iff₀ hR).mp hi
    rw [pow_succ] at hh
    dsimp [s]
    nlinarith
  have hq₁ : (∫ y in Metric.ball a r,‖G y-q i‖^2)≤C*(2*r)^(2+2*β) := by
    apply (plane_L2_sub_const_mono G (q i) (Metric.ball_subset_ball hrsi)).trans
    exact (hq i).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (hs i).le hsir (by linarith)) hC)
  have hq₂ : (∫ y in Metric.ball a r,‖G y-q₀‖^2)≤C*(2*r)^(2+2*β) :=
    hq₀.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hr.le (by linarith : r≤2*r) (by linarith)) hC)
  have hnear : dist (q i) q₀≤M*(2*r)^β := by
    apply campanato_constant_distance G (by positivity : 0<2*r) hC
    · simpa only [mul_div_cancel_left₀ r (by norm_num : (2:ℝ)≠0)] using hq₁
    · simpa only [mul_div_cancel_left₀ r (by norm_num : (2:ℝ)≠0)] using hq₂
  calc
    _ ≤ dist H (q i)+dist (q i) q₀ := dist_triangle _ _ _
    _ ≤ M/(1-θ)*(s i)^β+M*(2*r)^β := add_le_add (happrox i) hnear
    _ ≤ M/(1-θ)*(2*r)^β+M*(2*r)^β := by
      apply add_le_add _ le_rfl
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (hs i).le hsir hβ.le) (by positivity)
    _ = _ := by rw [Real.mul_rpow (by norm_num) hr.le]; dsimp [M,θ]; ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma campanato_holder_field (G : Lp Plane 2 (volume : Measure Plane))
    {R C β s : ℝ} (hR : 0<R) (hC : 0≤C) (hβ : 0<β) (hs : 0<s) (hsR : 4*s≤R)
    (hosc : ∀ x∈Metric.ball (0 : Plane) s,∀ r : ℝ,0<r → r≤R → ∃ q : Plane,
      (∫ y in Metric.ball x r,‖G y-q‖^2)≤C*r^(2+2*β)) :
    ∃ H : Plane → Plane,∃ K L : ℝ,0≤K ∧ 0≤L ∧
      (∀ x∈Metric.ball (0 : Plane) s,∀ y∈Metric.ball (0 : Plane) s,
        dist (H x) (H y)≤K*(dist x y)^β) ∧
      (∀ x∈Metric.ball (0 : Plane) s,∀ r : ℝ,0<r → r≤R → ∀ q : Plane,
        (∫ y in Metric.ball x r,‖G y-q‖^2)≤C*r^(2+2*β) → dist (H x) q≤L*r^β) := by
  classical
  let L : ℝ := 4*Real.sqrt C*(1+1/(1-(1/2:ℝ)^β))*2^β
  have hθ : (1/2:ℝ)^β<1 := Real.rpow_lt_one (by norm_num) (by norm_num) hβ
  have hL : 0≤L := by dsimp [L]; positivity
  have hex := fun (x : Plane) (hx : x∈Metric.ball (0 : Plane) s) ↦
    campanato_point_limit G x hR hC hβ (hosc x hx)
  choose H₀ hH₀ using hex
  let H : Plane → Plane := fun x ↦
    if hx : x∈Metric.ball (0 : Plane) s then H₀ x hx else H₀ 0 (Metric.mem_ball_self hs)
  have hH (x : Plane) (hx : x∈Metric.ball (0 : Plane) s) (r : ℝ) (hr : 0<r) (hrR : r≤R)
      (q : Plane) (hq : (∫ y in Metric.ball x r,‖G y-q‖^2)≤C*r^(2+2*β)) :
      dist (H x) q≤L*r^β := by
    simpa only [H,dite_eq_left hx] using hH₀ x hx r hr hrR q hq
  refine ⟨H,(2*L+4*Real.sqrt C)*2^β,L,by positivity,hL,?_,hH⟩
  intro x hx y hy
  by_cases hxy : x=y
  · subst y; simp [Real.zero_rpow hβ.ne']
  have hd : 0<dist x y := dist_pos.mpr hxy
  let r := 2*dist x y
  have hr : 0<r := by dsimp [r]; positivity
  have hrR : r≤R := by
    have hh := dist_triangle x (0 : Plane) y
    have hx' : dist x 0<s := hx
    have hy' : dist y 0<s := hy
    rw [dist_comm (0 : Plane) y] at hh
    dsimp [r]; linarith
  obtain ⟨q,hq⟩ := hosc x hx r hr hrR
  obtain ⟨q',hq'⟩ := hosc y hy r hr hrR
  have hsub : Metric.ball x (r/2)⊆Metric.ball y r := by
    intro z hz
    have hz' : dist z x<r/2 := hz
    have hh := dist_triangle z x y
    change dist z y<r
    dsimp [r] at *; linarith
  have h₁ : (∫ z in Metric.ball x (r/2),‖G z-q‖^2)≤C*r^(2+2*β) :=
    (plane_L2_sub_const_mono G q (Metric.ball_subset_ball (by linarith))).trans hq
  have h₂ : (∫ z in Metric.ball x (r/2),‖G z-q'‖^2)≤C*r^(2+2*β) :=
    (plane_L2_sub_const_mono G q' hsub).trans hq'
  have hnear := campanato_constant_distance G hr hC h₁ h₂
  have hxq := hH x hx r hr hrR q hq
  have hyq := hH y hy r hr hrR q' hq'
  calc
    _ ≤ dist (H x) q+dist q q'+dist q' (H y) := dist_triangle4 _ _ _ _
    _ ≤ L*r^β+4*Real.sqrt C*r^β+L*r^β :=
      add_le_add (add_le_add hxq hnear) (by simpa only [dist_comm] using hyq)
    _ = _ := by dsimp [r]; rw [Real.mul_rpow (by norm_num) dist_nonneg]; ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma plane_closedBall_ae_ball (a : Plane) (r : ℝ) :
    Metric.closedBall a r =ᵐ[(volume : Measure Plane)] Metric.ball a r := by
  have hh : ∀ᵐ x ∂(volume : Measure Plane),x∉Metric.sphere a r := by
    rw [ae_iff]
    simpa only [not_not,Set.ofPred_mem_eq] using Measure.addHaar_sphere (volume : Measure Plane) a r
  filter_upwards [hh] with x hx
  change dist x a ≠ r at hx
  apply propext
  change (dist x a≤r) ↔ (dist x a<r)
  exact ⟨fun h ↦ lt_of_le_of_ne h hx,le_of_lt⟩

lemma campanato_average_distance (G : Lp Plane 2 (volume : Measure Plane))
    {a q : Plane} {r C β : ℝ} (hr : 0<r) (hC : 0≤C)
    (h : (∫ y in Metric.ball a r,‖G y-q‖^2)≤C*r^(2+2*β)) :
    dist (⨍ y in Metric.ball a r,G y) q≤Real.sqrt C*r^β := by
  let S := Metric.ball a r
  let m : ℝ := volume.real S
  have hm : m=Real.pi*r^2 := plane_ball_real_at a hr.le
  have hmpos : 0 < m := by rw [hm]; positivity
  let : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hG : IntegrableOn (fun y ↦ G y) S :=
    ((Lp.memLp G).restrict S).integrable (by norm_num)
  have hc : IntegrableOn (fun _ : Plane ↦ q) S := integrableOn_const measure_ball_lt_top.ne
  have hnorm := (hG.sub hc).norm
  have hi := plane_L2_sub_const_integrable_at G q a r
  have hh := integral_square_le_mass hnorm hi
  simp only [Pi.sub_apply] at hh
  have hm' : (volume.restrict S).real univ=m := by simp [Measure.real,m]
  rw [hm'] at hh
  have hpow : r^(2+2*β)=r^2*(r^β)^2 := by
    rw [Real.rpow_add hr,Real.rpow_two,mul_comm (2:ℝ) β,Real.rpow_mul hr.le,Real.rpow_two]
  have hbound : (∫ y in S,‖G y-q‖)≤ m*(Real.sqrt C*r^β) := by
    have hπ : (1:ℝ)≤Real.pi := by linarith [Real.pi_gt_three]
    have haux : m*(C*r^(2+2*β))≤(m*(Real.sqrt C*r^β))^2 := by
      rw [hpow,mul_pow,mul_pow,Real.sq_sqrt hC]
      have hh' : r^2≤ m := by rw [hm]; nlinarith [sq_nonneg r]
      have hh'' := mul_le_mul_of_nonneg_left hh' (mul_nonneg hmpos.le
        (mul_nonneg hC (sq_nonneg (r^β))))
      nlinarith
    have hs := hh.trans ((mul_le_mul_of_nonneg_left h hmpos.le).trans haux)
    have hn : 0≤ m*(Real.sqrt C*r^β) := by positivity
    nlinarith
  have havg : (⨍ y in S,G y)-q=m⁻¹ • (∫ y in S,G y-q) := by
    rw [setAverage_eq,integral_sub hG hc,integral_const]
    rw [hm']
    change m⁻¹ • (∫ y in S,G y)-q=m⁻¹ • ((∫ y in S,G y)-m • q)
    rw [smul_sub,smul_smul,inv_mul_cancel₀ hmpos.ne',one_smul]
  rw [dist_eq_norm,havg,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hmpos)]
  calc
    _ ≤ m⁻¹*(∫ y in S,‖G y-q‖) := mul_le_mul_of_nonneg_left
      (norm_integral_le_integral_norm _) (inv_nonneg.mpr hmpos.le)
    _ ≤ m⁻¹*(m*(Real.sqrt C*r^β)) := mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hmpos.le)
    _ = _ := by rw [← mul_assoc,inv_mul_cancel₀ hmpos.ne',one_mul]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma campanato_identify_ae (G : Lp Plane 2 (volume : Measure Plane))
    {S : Set Plane} (hS : MeasurableSet S) {H : Plane → Plane} {R C β L : ℝ}
    (hR : 0<R) (hC : 0≤C) (hβ : 0<β)
    (hosc : ∀ x∈S,∀ r : ℝ,0<r → r≤R → ∃ q : Plane,
      (∫ y in Metric.ball x r,‖G y-q‖^2)≤C*r^(2+2*β))
    (hH : ∀ x∈S,∀ r : ℝ,0<r → r≤R → ∀ q : Plane,
      (∫ y in Metric.ball x r,‖G y-q‖^2)≤C*r^(2+2*β) → dist (H x) q≤L*r^β) :
    H =ᵐ[volume.restrict S] (G : Plane → Plane) := by
  have hLeb := IsUnifLocDoublingMeasure.ae_tendsto_average (volume : Measure Plane)
    ((Lp.memLp G).locallyIntegrable (by norm_num)) 1
  apply (ae_restrict_iff' hS).mpr
  filter_upwards [hLeb] with x hx hxS
  let s : ℕ → ℝ := fun i ↦ (1/2:ℝ)^i*R
  have hs (i : ℕ) : 0<s i := by dsimp [s]; positivity
  have hsR (i : ℕ) : s i≤R := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (pow_le_one₀ (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)≤1)) hR.le
  have hs0 : Tendsto s atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2)
        (by norm_num : (1/2:ℝ)<1)).mul_const R
  have hs0' : Tendsto s atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr
    ⟨hs0,Eventually.of_forall hs⟩
  have hLeb' := hx (fun _ : ℕ ↦ x) s hs0' (Eventually.of_forall fun i ↦ by
    simpa only [one_mul,Metric.mem_closedBall,dist_self] using (hs i).le)
  have hLebBall : Tendsto (fun i ↦ ⨍ y in Metric.ball x (s i),G y) atTop (𝓝 (G x)) := by
    convert hLeb' using 1
    funext i
    exact (setAverage_congr (f := fun y ↦ G y) (plane_closedBall_ae_ball x (s i))).symm
  have hβlim : Tendsto (fun i ↦ (Real.sqrt C+L)*(s i)^β) atTop (𝓝 0) := by
    simpa only [Real.zero_rpow hβ.ne',mul_zero] using
      (hs0.rpow_const (Or.inr hβ.le)).const_mul (Real.sqrt C+L)
  have hlim : Tendsto (fun i ↦ ⨍ y in Metric.ball x (s i),G y) atTop (𝓝 (H x)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun _ ↦ dist_nonneg) _ hβlim
    intro i
    obtain ⟨q,hq⟩ := hosc x hxS (s i) (hs i) (hsR i)
    calc
      _ ≤ dist (⨍ y in Metric.ball x (s i),G y) q+dist q (H x) := dist_triangle _ _ _
      _ ≤ Real.sqrt C*(s i)^β+L*(s i)^β := add_le_add
        (campanato_average_distance G (hs i) hC hq)
        (by simpa only [dist_comm] using hH x hxS (s i) (hs i) (hsR i) q hq)
      _ = _ := by ring
  exact tendsto_nhds_unique hlim hLebBall

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma continuousOn_of_power_distance {F : Plane → Plane} {S : Set Plane}
    {K β : ℝ} (hβ : 0<β)
    (h : ∀ x∈S,∀ y∈S,dist (F x) (F y)≤K*(dist x y)^β) : ContinuousOn F S := by
  intro x hx
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hd : Tendsto (fun y : Plane ↦ dist y x) (𝓝[S] x) (𝓝 0) := by
    have hc : ContinuousAt (fun y : Plane ↦ dist y x) x :=
      ((continuous_id : Continuous (fun y : Plane ↦ y)).dist continuous_const).continuousAt
    simpa only [dist_self] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hb : Tendsto (fun y : Plane ↦ K*(dist y x)^β) (𝓝[S] x) (𝓝 0) := by
    simpa only [Real.zero_rpow hβ.ne',mul_zero] using (hd.rpow_const (Or.inr hβ.le)).const_mul K
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ dist_nonneg) _ hb
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact h y hy x hx

theorem plane_campanato_regularity (G : Lp Plane 2 (volume : Measure Plane))
    {R C β s : ℝ} (hR : 0<R) (hC : 0≤C) (hβ : 0<β) (hs : 0<s) (hsR : 4*s≤R)
    (hosc : ∀ x∈Metric.ball (0 : Plane) s,∀ r : ℝ,0<r → r≤R → ∃ q : Plane,
      (∫ y in Metric.ball x r,‖G y-q‖^2)≤C*r^(2+2*β)) :
    ∃ H : Plane → Plane,∃ K : ℝ,0≤K ∧ ContinuousOn H (Metric.ball 0 s) ∧
      H =ᵐ[volume.restrict (Metric.ball (0 : Plane) s)] (G : Plane → Plane) ∧
      ∀ x∈Metric.ball (0 : Plane) s,∀ y∈Metric.ball (0 : Plane) s,
        dist (H x) (H y)≤K*(dist x y)^β := by
  obtain ⟨H,K,L,hK,hL,hHolder,happrox⟩ := campanato_holder_field G hR hC hβ hs hsR hosc
  exact ⟨H,K,hK,continuousOn_of_power_distance hβ hHolder,
    campanato_identify_ae G measurableSet_ball hR hC hβ hosc happrox,hHolder⟩

theorem cmc_linearized_holder_gradient {p : Plane → Plane} (hp : Continuous p)
    (hpb : ∀ y,‖p y‖≤1) {R α D : ℝ} (hR : 0<R) (hα : 0<α) (hα1 : α≤1) (hD : 0≤D)
    (hHolder : ∀ x∈Metric.ball (0 : Plane) R,∀ y∈Metric.ball (0 : Plane) R,
      ‖cmcJacobian (p x)-cmcJacobian (p y)‖≤D*(dist x y)^α)
    (u : Lp ℝ 2 (volume : Measure Plane)) (G : Lp Plane 2 (volume : Measure Plane))
    (hg : PlaneWeakGradient (Metric.ball 0 R) u G)
    (hd : ∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆Metric.ball 0 R → (∫ y,fderiv ℝ ψ y (cmcJacobian (p y) (G y)))=0) :
    ∃ H : Plane → Plane,∃ s K β : ℝ,0<s ∧ s≤R/4 ∧ 0≤K ∧ 0<β ∧ β≤1 ∧
      ContinuousOn H (Metric.ball 0 s) ∧
      H =ᵐ[volume.restrict (Metric.ball (0 : Plane) s)] (G : Plane → Plane) ∧
      ∀ x∈Metric.ball (0 : Plane) s,∀ y∈Metric.ball (0 : Plane) s,
        dist (H x) (H y)≤K*(dist x y)^β := by
  obtain ⟨r,C,γ,hr,hC,hγ,hγ1,hosc⟩ := cmc_uniform_oscillation hp hpb hR hα hα1 hD hHolder u G hg hd
  let s := min (R/4) (r/4)
  have hs : 0<s := lt_min (by positivity) (by positivity)
  have hsR : s≤R/4 := min_le_left _ _
  have hsr : 4*s≤r := by have := min_le_right (R/4) (r/4); dsimp [s]; linarith
  have hh : ∀ x∈Metric.ball (0 : Plane) s,∀ ρ : ℝ,0<ρ → ρ≤r → ∃ q : Plane,
      (∫ y in Metric.ball x ρ,‖G y-q‖^2)≤C*ρ^(2+2*(γ/2)) := by
    intro x hx ρ hρ hρr
    simpa only [mul_div_cancel₀ γ (by norm_num : (2:ℝ)≠0)] using
      hosc x ((Metric.ball_subset_ball hsR) hx) ρ hρ hρr
  obtain ⟨H,K,hK,hHc,hHe,hHp⟩ := plane_campanato_regularity G hr hC (half_pos hγ) hs hsr hh
  exact ⟨H,s,K,γ/2,hs,hsR,hK,half_pos hγ,by linarith,hHc,hHe,hHp⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

end CubicTorus
end
end
end

end OAI
