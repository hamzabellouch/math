import OAI.Analysis.ModularRecovery.CanonicalTomita

namespace OAI

/-! Equivalence of the modular and vector-state centralizers. -/

universe u

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace RealSpectralCalculus

lemma bandMultiplier_of_fixed (D : RealSpectralCalculus H) {x : H}
    (hx : ∀ t, D.unitary t x=x) {rho : ℝ} (hrho : 0 < rho) :
    D.calculus (bandMultiplier 0 rho) x=x := by
  rw [D.calculus_apply_eq_integral _ _ (bandKernel_integrable hrho) (bandMultiplier_fourier hrho)]
  simp only [hx]
  rw [integral_smul_const]
  have he := bandMultiplier_fourier (s := 0) hrho 0
  have hzero : bandMultiplier 0 rho 0=1 := bandMultiplier_one hrho ⟨by linarith,by linarith⟩
  simp only [mul_zero,Complex.ofReal_zero,zero_mul,Complex.exp_zero,mul_one,hzero] at he
  rw [← he,one_smul]

lemma spectralSupport_of_fixed (D : RealSpectralCalculus H) {x : H}
    (hx : ∀ t, D.unitary t x=x) : D.HasSpectralSupport {0} x := by
  intro f hf
  have hf0 : f 0=0 := hf 0 (mem_singleton 0)
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  apply le_of_forall_pos_le_add
  intro eps heps
  have hden : 0 < ‖x‖+1 := by positivity
  obtain ⟨d,hd,hdf⟩ := Metric.continuousAt_iff.mp f.continuous.continuousAt
    (eps/(‖x‖+1)) (div_pos heps hden)
  have hrho : 0 < d/4 := by positivity
  have hnorm : ‖f*bandMultiplier 0 (d/4)‖ ≤ eps/(‖x‖+1) := by
    apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
    intro u
    change ‖f u*bandMultiplier 0 (d/4) u‖ ≤ _
    by_cases hu : u ∈ Icc (0-2*(d/4)) (0+2*(d/4))
    · have hud : dist u 0 < d := by
        rw [Real.dist_eq,sub_zero,abs_lt]
        constructor <;> linarith [hu.1,hu.2]
      have hfu : ‖f u‖ < eps/(‖x‖+1) := by
        simpa only [hf0,dist_zero_right] using hdf hud
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left
        ((bandMultiplier 0 (d/4)).norm_coe_le_norm u |>.trans (norm_bandMultiplier_le _ _))
        (norm_nonneg _)).trans (by simpa only [mul_one] using hfu.le)
    · rw [bandMultiplier_zero hrho hu,mul_zero,norm_zero]
      positivity
  have heq : D.calculus f x=D.calculus (f*bandMultiplier 0 (d/4)) x := by
    rw [map_mul]
    change D.calculus f x=D.calculus f (D.calculus (bandMultiplier 0 (d/4)) x)
    rw [D.bandMultiplier_of_fixed hx hrho]
  rw [heq,zero_add]
  calc
    _ ≤ ‖f*bandMultiplier 0 (d/4)‖*‖x‖ := D.norm_calculus_apply_le _ _
    _ ≤ (eps/(‖x‖+1))*‖x‖ := mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
    _ ≤ eps := by rw [div_mul_eq_mul_div,div_le_iff₀ hden]; nlinarith

lemma halfGraph_of_fixed (D : RealSpectralCalculus H) {x : H}
    (hx : ∀ t, D.unitary t x=x) : (x,x) ∈ D.halfGraph := by
  have hs := D.spectralSupport_of_fixed hx
  have he (n : ℕ) : D.calculus (halfExponentialCutoff n) x=x := by
    apply hs.fixed
    intro u hu
    rcases mem_singleton_iff.mp hu with rfl
    change (Real.exp (min (n:ℝ) 0/2):ℂ)=1
    rw [min_eq_right (Nat.cast_nonneg n)]
    norm_num
  change Tendsto (fun n => D.calculus (halfExponentialCutoff n) x) atTop (𝓝 x)
  simpa only [he] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => x) atTop (𝓝 x))

lemma fixed_of_halfGraph (D : RealSpectralCalculus H) {x : H}
    (hx : (x,x) ∈ D.halfGraph) : ∀ t, D.unitary t x=x := by
  have hr : D.calculus halfResolvent x=(1/2:ℂ) • x := by
    have he := (D.halfGraph_iff_resolvent x x).mp hx
    rw [map_add] at he
    calc
      D.calculus halfResolvent x=(1/2:ℂ) •
          (D.calculus halfResolvent x+D.calculus halfResolvent x) := by
        rw [smul_add,← add_smul]
        norm_num
      _ = _ := by rw [he]
  have hs : D.HasSpectralSupport {0} x := by
    intro f hf
    apply D.kernel_of_separated_zero centeredHalfResolvent 0 centeredHalfResolvent_separated _ f
      (hf 0 (mem_singleton 0))
    rw [realMultiplier_centeredHalfResolvent,map_sub,map_smul,map_one,sub_apply,
      smul_apply,one_apply_eq_self,hr,sub_self]
  intro t
  exact hs.fixed (by intro u hu; rcases mem_singleton_iff.mp hu with rfl; simp)

end RealSpectralCalculus
namespace StandardModularData

def InStateCentralizer (S : StandardModularData H) (a : H →L[ℂ] H) : Prop :=
  a ∈ S.M ∧ ∀ b : H →L[ℂ] H, b ∈ S.M → S.state (a*b)=S.state (b*a)

def StateScalarCentralizer (S : StandardModularData H) : Prop :=
  ∀ a : H →L[ℂ] H, S.InStateCentralizer a → ∃ c : ℂ, a=c • (1:H →L[ℂ] H)

lemma state_mul_inner (S : StandardModularData H) (a b : H →L[ℂ] H) :
    S.state (a*b)=inner ℂ ((star a) S.xi) (b S.xi) :=
  (ContinuousLinearMap.adjoint_inner_left a (b S.xi) S.xi).symm

lemma fixed_mem_stateCentralizer (S : StandardModularData H) {a : H →L[ℂ] H}
    (ha : a ∈ S.M) (hfix : ∀ t, S.sigma t a=a) : S.InStateCentralizer a := by
  have hv : ∀ t, S.D.unitary t ((star a) S.xi)=(star a) S.xi := by
    intro t
    rw [← S.sigma_apply_xi,S.sigma_star,hfix]
  have hg := S.D.halfGraph_of_fixed hv
  have hJ : S.J (a S.xi)=(star a) S.xi :=
    S.D.halfGraph_unique (by simpa only [star_star] using S.core_halfGraph (star a) (star_mem ha)) hg
  refine ⟨ha,fun b hb => ?_⟩
  rw [S.state_mul_inner,S.state_mul_inner]
  calc
    inner ℂ ((star a) S.xi) (b S.xi) = inner ℂ ((star a) S.xi) (S.J ((star b) S.xi)) :=
      S.D.halfGraph_symmetric hg (S.core_halfGraph b hb)
    _ = inner ℂ (S.J (a S.xi)) (S.J ((star b) S.xi)) := by rw [hJ]
    _ = inner ℂ ((star b) S.xi) (a S.xi) := by
      rw [antiunitary_inner]
      exact inner_conj_symm _ _

lemma stateCentralizer_fixed (S : StandardModularData H) {a : H →L[ℂ] H}
    (ha : S.InStateCentralizer a) : ∀ t, S.sigma t a=a := by
  have hrev : (S.J ((star a) S.xi), a S.xi) ∈ S.D.halfGraph := by
    rw [S.D.halfGraph_adjoint_iff]
    have hc : closure {p : H × H | ∃ b : H →L[ℂ] H,
        b ∈ S.M ∧ p=(b S.xi,(star b) S.xi)} ⊆
        {p | inner ℂ (S.J p.2) (S.J ((star a) S.xi))=inner ℂ p.1 (a S.xi)} := by
      apply closure_minimal
      · rintro p ⟨b,hb,rfl⟩
        change inner ℂ (S.J ((star b) S.xi)) (S.J ((star a) S.xi)) =
          inner ℂ (b S.xi) (a S.xi)
        calc
          _ = inner ℂ ((star a) S.xi) ((star b) S.xi) := by
            rw [antiunitary_inner]
            exact inner_conj_symm _ _
          _ = S.state (a*star b) := (S.state_mul_inner a (star b)).symm
          _ = S.state (star b*a) := ha.2 (star b) (star_mem hb)
          _ = _ := by rw [S.state_mul_inner,star_star]
      · exact isClosed_eq (by fun_prop) (by fun_prop)
    intro x y hxy
    have ht : (x,S.J y) ∈ closure {p : H × H | ∃ b : H →L[ℂ] H,
        b ∈ S.M ∧ p=(b S.xi,(star b) S.xi)} := by
      rw [S.tomita_graph]
      exact ⟨y,hxy,rfl⟩
    have he := hc ht
    change inner ℂ (S.J (S.J y)) (S.J ((star a) S.xi))=inner ℂ x (a S.xi) at he
    rw [S.conjugation] at he
    simpa only [Complex.star_def,inner_conj_symm] using (congrArg star he).symm
  have hcore := S.core_halfGraph a ha.1
  have hp := S.D.halfGraph_nonneg (S.D.halfGraph_sub hcore hrev)
  have he : S.J ((star a) S.xi)-a S.xi=-(a S.xi-S.J ((star a) S.xi)) := by abel
  rw [he,inner_neg_right,Complex.neg_re] at hp
  change 0 ≤ -RCLike.re (inner ℂ (a S.xi-S.J ((star a) S.xi))
    (a S.xi-S.J ((star a) S.xi))) at hp
  rw [← norm_sq_eq_re_inner] at hp
  have hn : ‖a S.xi-S.J ((star a) S.xi)‖=0 := by
    nlinarith [norm_nonneg (a S.xi-S.J ((star a) S.xi))]
  have heq := sub_eq_zero.mp (norm_eq_zero.mp hn)
  apply S.fixed_of_fixed_vector ha.1
  apply S.D.fixed_of_halfGraph
  rwa [← heq] at hcore

lemma inStateCentralizer_iff_fixed (S : StandardModularData H) (a : H →L[ℂ] H) :
    S.InStateCentralizer a ↔ a ∈ S.M ∧ ∀ t, S.sigma t a=a :=
  ⟨fun h => ⟨h.1,S.stateCentralizer_fixed h⟩,
    fun h => S.fixed_mem_stateCentralizer h.1 h.2⟩

lemma scalarCentralizer_of_state (S : StandardModularData H)
    (hs : S.StateScalarCentralizer) : S.ScalarCentralizer := by
  intro a ha hfix
  exact hs a (S.fixed_mem_stateCentralizer ha hfix)

lemma scalarCentralizer_iff_state (S : StandardModularData H) :
    S.ScalarCentralizer ↔ S.StateScalarCentralizer := by
  constructor
  · intro hs a ha
    exact hs a ha.1 (S.stateCentralizer_fixed ha)
  · exact S.scalarCentralizer_of_state

end StandardModularData
end BoundedRecovery

end

end OAI
