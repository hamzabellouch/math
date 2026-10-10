import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CountertermEvaluation
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarWellNumerics
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.VerticalCutoffProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.RawDensitySample

namespace OAI

/-! A rational scalar evaluator for the actual manufactured well field.
The well-depth factors are clipped to their proved interval [1,2]. This
stabilizes every encoded input and preserves the valid-instance estimate. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb.ManufacturedFieldEvaluation

def coefficient (rho p : ℕ) (scale : ℚ) (sites : List (ℚ×ℚ)) (a : ℚ×ℚ) : ℚ :=
  1+RationalSmoothTransition.clip (CountertermEvaluation.row rho p a sites/scale)

def translate (r a : ℚ×ℚ) : ℚ×ℚ := (r.1-a.1,r.2-a.2)

def planar (rho p : ℕ) (scale : ℚ) (sites : List (ℚ×ℚ)) (r : ℚ×ℚ) : ℚ :=
  (sites.map (fun a => coefficient rho p scale sites a *
    PlanarWellNumerics.approximate p (translate r a))).sum

def rawValue (rho p : ℕ) (scale S : ℚ) (sites : List (ℚ×ℚ))
    (x : CappedKernelProgram.Triple) : ℚ :=
  RationalSmoothTransition.clip (VerticalCutoffProgram.value (p,(S,x.2.2))) *
    planar rho p scale sites (x.1,x.2.1)

theorem coefficient_bounds (rho p : ℕ) (scale : ℚ) (sites : List (ℚ×ℚ)) (a : ℚ×ℚ) :
    1 ≤ coefficient rho p scale sites a ∧ coefficient rho p scale sites a ≤ 2 := by
  have h := RationalSmoothTransition.clip_bounds (CountertermEvaluation.row rho p a sites/scale)
  unfold coefficient
  constructor <;> linarith

theorem translate_position (r a : ℚ×ℚ) :
    PlanarForcingProgram.position (translate r a) =
      PlanarForcingProgram.position r-PlanarForcingProgram.position a := by
  ext i
  fin_cases i <;> simp [translate,PlanarForcingProgram.position]

theorem coefficient_error (rho p : ℕ) (hrho : 0 < rho) {scale : ℚ}
    (hscale : (1:ℝ) ≤ scale) {m : ℕ} (u : Fin m → ℚ×ℚ) (hu : Function.Injective u)
    (i : Fin m)
    (hc : localizedCounterterm (GaussianFrequency.frequency rho)
      (fun j => PlanarForcingProgram.position (u j)) i ≤ scale) :
    |(coefficient rho p scale (List.ofFn u) (u i):ℝ)-
      (1+localizedCounterterm (GaussianFrequency.frequency rho)
        (fun j => PlanarForcingProgram.position (u j)) i/(scale:ℝ))| ≤
      (m:ℝ)*2*(CountertermEvaluation.guard rho:ℝ)^3*((p:ℝ)+1)⁻¹ := by
  let c := localizedCounterterm (GaussianFrequency.frequency rho)
    (fun j => PlanarForcingProgram.position (u j)) i
  let E := (m:ℝ)*2*(CountertermEvaluation.guard rho:ℝ)^3*((p:ℝ)+1)⁻¹
  have hs : (0:ℝ) < scale := by linarith
  have he : |((CountertermEvaluation.row rho p (u i) (List.ofFn u)/scale:ℚ):ℝ)-
      c/(scale:ℝ)| ≤ E := by
    rw [Rat.cast_div,← sub_div,abs_div,abs_of_pos hs]
    exact ((div_le_div_of_nonneg_right (CountertermEvaluation.row_error rho p hrho u hu i)
      hs.le).trans (div_le_self (by positivity) hscale))
  have hc0 : 0 ≤ c/(scale:ℝ) := div_nonneg (localizedCounterterm_nonnegative _ _ _) hs.le
  have hc1 : c/(scale:ℝ) ≤ 1 := (div_le_one hs).mpr hc
  simpa only [coefficient,Rat.cast_add,Rat.cast_one,add_sub_add_left_eq_sub]
    using RationalSmoothTransition.clip_error _ hc0 hc1 he

theorem well_abs_le_guard (rho : ℕ) (r : PlanarPosition) :
    |manufacturedPlanarWell r| ≤ (CountertermEvaluation.guard rho:ℝ) := by
  have h := planarWellDerivativeConstant_bound (k := 0) (by omega) r
  rw [norm_iteratedFDeriv_zero,Real.norm_eq_abs] at h
  exact h.trans (CountertermEvaluation.guard_bounds rho).2.2.2

private theorem product_error {a a' b b' A B ε η : ℝ}
    (ha : |a'| ≤ A) (hb : |b| ≤ B) (he : |a'-a| ≤ ε) (hf : |b'-b| ≤ η) :
    |a'*b'-a*b| ≤ A*η+ε*B := by
  have hA : 0 ≤ A := (abs_nonneg _).trans ha
  have he0 : 0 ≤ ε := (abs_nonneg _).trans he
  rw [show a'*b'-a*b = a'*(b'-b)+(a'-a)*b by ring]
  exact (abs_add_le _ _).trans (by
    rw [abs_mul,abs_mul]
    exact add_le_add (mul_le_mul ha hf (abs_nonneg _) hA)
      (mul_le_mul he hb (abs_nonneg _) he0))

theorem planar_error (rho p : ℕ) (hrho : 0 < rho) {scale : ℚ}
    (hscale : (1:ℝ) ≤ scale) {m : ℕ} (u : Fin m → ℚ×ℚ) (hu : Function.Injective u)
    (hc : ∀ i, localizedCounterterm (GaussianFrequency.frequency rho)
      (fun j => PlanarForcingProgram.position (u j)) i ≤ scale) (r : ℚ×ℚ) :
    |(planar rho p scale (List.ofFn u) r:ℝ)-
      countertermWellSum (GaussianFrequency.frequency rho) scale
        (fun i => PlanarForcingProgram.position (u i)) (PlanarForcingProgram.position r)| ≤
      ((m:ℝ)*2+(m:ℝ)^2*2*(CountertermEvaluation.guard rho:ℝ)^4)*((p:ℝ)+1)⁻¹ := by
  rw [planar,List.map_ofFn,List.sum_ofFn,Rat.cast_sum]
  unfold countertermWellSum
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  have hs : ∀ i : Fin m,
      |(coefficient rho p scale (List.ofFn u) (u i):ℝ) *
          (PlanarWellNumerics.approximate p (translate r (u i)):ℝ)-
        (1+localizedCounterterm (GaussianFrequency.frequency rho)
          (fun j => PlanarForcingProgram.position (u j)) i/(scale:ℝ))*
          manufacturedPlanarWell (PlanarForcingProgram.position r-PlanarForcingProgram.position (u i))| ≤
      2*((p:ℝ)+1)⁻¹+
        ((m:ℝ)*2*(CountertermEvaluation.guard rho:ℝ)^3*((p:ℝ)+1)⁻¹)*
          (CountertermEvaluation.guard rho:ℝ) := by
    intro i
    have hb := coefficient_bounds rho p scale (List.ofFn u) (u i)
    have hab : |(coefficient rho p scale (List.ofFn u) (u i):ℝ)| ≤ 2 := by
      have hl : (1:ℝ) ≤ coefficient rho p scale (List.ofFn u) (u i) := by exact_mod_cast hb.1
      have hh : (coefficient rho p scale (List.ofFn u) (u i):ℝ) ≤ 2 := by exact_mod_cast hb.2
      rw [abs_of_nonneg (by linarith)]
      exact hh
    have he := PlanarWellNumerics.approximation_error p (translate r (u i))
    rw [translate_position] at he
    exact product_error hab (well_abs_le_guard rho _) (coefficient_error rho p hrho hscale u hu i (hc i)) he
  calc
    _ ≤ ∑ _i : Fin m, (2*((p:ℝ)+1)⁻¹+
        ((m:ℝ)*2*(CountertermEvaluation.guard rho:ℝ)^3*((p:ℝ)+1)⁻¹)*
          (CountertermEvaluation.guard rho:ℝ)) := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [Function.comp_apply,Rat.cast_mul] using hs i
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      ring

theorem planar_exact_bound (rho : ℕ) {scale : ℚ} (hscale : (1:ℝ) ≤ scale)
    {m : ℕ} (u : Fin m → ℚ×ℚ)
    (hc : ∀ i, localizedCounterterm (GaussianFrequency.frequency rho)
      (fun j => PlanarForcingProgram.position (u j)) i ≤ scale) (r : PlanarPosition) :
    |countertermWellSum (GaussianFrequency.frequency rho) scale
      (fun i => PlanarForcingProgram.position (u i)) r| ≤
      2*(m:ℝ)*(CountertermEvaluation.guard rho:ℝ) := by
  have hs : (0:ℝ) < scale := by linarith
  unfold countertermWellSum
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _i : Fin m, 2*(CountertermEvaluation.guard rho:ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      have hc0 := div_nonneg (localizedCounterterm_nonnegative
        (GaussianFrequency.frequency rho) (fun j => PlanarForcingProgram.position (u j)) i) hs.le
      have hc1 := (div_le_one hs).mpr (hc i)
      rw [abs_mul,abs_of_nonneg (by linarith : 0 ≤ 1+
        localizedCounterterm (GaussianFrequency.frequency rho)
          (fun j => PlanarForcingProgram.position (u j)) i/(scale:ℝ))]
      exact mul_le_mul (by linarith) (well_abs_le_guard rho _) (abs_nonneg _) (by norm_num)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      ring

theorem raw_error (rho p : ℕ) (hrho : 0 < rho) {scale : ℚ}
    (hscale : (1:ℝ) ≤ scale) (S : ℚ) {m : ℕ} (u : Fin m → ℚ×ℚ)
    (hu : Function.Injective u)
    (hc : ∀ i, localizedCounterterm (GaussianFrequency.frequency rho)
      (fun j => PlanarForcingProgram.position (u j)) i ≤ scale)
    (x : CappedKernelProgram.Triple) :
    |(rawValue rho p scale S (List.ofFn u) x:ℝ)-
      manufacturedWellField (GaussianFrequency.frequency rho) scale S
        (fun i => PlanarForcingProgram.position (u i)) (CappedKernelProgram.position x)| ≤
      (2*(m:ℝ)+2*(m:ℝ)*(CountertermEvaluation.guard rho:ℝ)+
        2*(m:ℝ)^2*(CountertermEvaluation.guard rho:ℝ)^4)*((p:ℝ)+1)⁻¹ := by
  have hcut := slabWellCutoff_bounds (S:ℝ) (x.2.2:ℝ)
  have hecut := RationalSmoothTransition.clip_error
    (VerticalCutoffProgram.value (p,(S,x.2.2))) hcut.1 hcut.2
    (VerticalCutoffProgram.approximation_error (p,(S,x.2.2)))
  have hcb := RationalSmoothTransition.clip_bounds (VerticalCutoffProgram.value (p,(S,x.2.2)))
  have hab : |(RationalSmoothTransition.clip (VerticalCutoffProgram.value (p,(S,x.2.2))):ℝ)| ≤ 1 := by
    have hl : (0:ℝ) ≤ RationalSmoothTransition.clip (VerticalCutoffProgram.value (p,(S,x.2.2))) :=
      by exact_mod_cast hcb.1
    have hh : (RationalSmoothTransition.clip (VerticalCutoffProgram.value (p,(S,x.2.2))):ℝ) ≤ 1 :=
      by exact_mod_cast hcb.2
    simpa only [abs_of_nonneg hl] using hh
  have he := product_error hab
    (planar_exact_bound rho hscale u hc (PlanarForcingProgram.position (x.1,x.2.1))) hecut
    (planar_error rho p hrho hscale u hu hc (x.1,x.2.1))
  calc
    _ ≤ 1*((m:ℝ)*2+(m:ℝ)^2*2*(CountertermEvaluation.guard rho:ℝ)^4)*((p:ℝ)+1)⁻¹+
        ((p:ℝ)+1)⁻¹*(2*(m:ℝ)*(CountertermEvaluation.guard rho:ℝ)) := by
      simpa only [rawValue,Rat.cast_mul,manufacturedWellField,RawDensitySample.position_split,
        Prod.fst,Prod.snd,one_mul] using he
    _ = _ := by ring

def precision (rho m P : ℕ) : ℕ := 16*(CountertermEvaluation.guard rho)^4*(m+1)^2*(P+1)

def value (rho P : ℕ) (scale S : ℚ) (sites : List (ℚ×ℚ))
    (x : CappedKernelProgram.Triple) : ℚ := rawValue rho (precision rho sites.length P) scale S sites x

theorem precision_budget (rho m P : ℕ) :
    (2*(m:ℝ)+2*(m:ℝ)*(CountertermEvaluation.guard rho:ℝ)+
      2*(m:ℝ)^2*(CountertermEvaluation.guard rho:ℝ)^4)*
        ((precision rho m P:ℝ)+1)⁻¹ ≤ ((P:ℝ)+1)⁻¹ := by
  let C : ℝ := CountertermEvaluation.guard rho
  let M : ℝ := m
  have hC : 1 ≤ C := by dsimp [C]; exact_mod_cast (CountertermEvaluation.guard_bounds rho).1
  have hM : 0 ≤ M := Nat.cast_nonneg _
  have hC4 : 1 ≤ C^4 := one_le_pow₀ hC
  have hc4 : C ≤ C^4 := le_self_pow₀ hC (by decide)
  have hm : M ≤ (M+1)^2 := by nlinarith
  have hm2 : M^2 ≤ (M+1)^2 := by nlinarith
  have h1 : M ≤ (M+1)^2*C^4 := hm.trans (le_mul_of_one_le_right (sq_nonneg _) hC4)
  have h2 : M*C ≤ (M+1)^2*C^4 := mul_le_mul hm hc4 (by linarith) (sq_nonneg _)
  have h3 : M^2*C^4 ≤ (M+1)^2*C^4 := mul_le_mul_of_nonneg_right hm2 (by positivity)
  have hb : 2*M+2*M*C+2*M^2*C^4 ≤ 16*C^4*(M+1)^2 := by nlinarith
  have hP : (0:ℝ) < (P:ℝ)+1 := by positivity
  have hprec : (precision rho m P:ℝ) = 16*C^4*(M+1)^2*((P:ℝ)+1) := by
    simp only [precision,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow,Nat.cast_add,Nat.cast_one,C,M]
  change (2*M+2*M*C+2*M^2*C^4)*((precision rho m P:ℝ)+1)⁻¹ ≤ ((P:ℝ)+1)⁻¹
  apply (mul_inv_le_iff₀ (by positivity : (0:ℝ) < (precision rho m P:ℝ)+1)).mpr
  rw [hprec]
  have heq : ((P:ℝ)+1)⁻¹*(16*C^4*(M+1)^2*((P:ℝ)+1)+1) =
      16*C^4*(M+1)^2+((P:ℝ)+1)⁻¹ := by field_simp
  rw [heq]
  exact hb.trans (le_add_of_nonneg_right (inv_nonneg.mpr hP.le))

theorem approximation_error (rho P : ℕ) (hrho : 0 < rho) {scale : ℚ}
    (hscale : (1:ℝ) ≤ scale) (S : ℚ) {m : ℕ} (u : Fin m → ℚ×ℚ)
    (hu : Function.Injective u)
    (hc : ∀ i, localizedCounterterm (GaussianFrequency.frequency rho)
      (fun j => PlanarForcingProgram.position (u j)) i ≤ scale)
    (x : CappedKernelProgram.Triple) :
    |(value rho P scale S (List.ofFn u) x:ℝ)-
      manufacturedWellField (GaussianFrequency.frequency rho) scale S
        (fun i => PlanarForcingProgram.position (u i)) (CappedKernelProgram.position x)| ≤
      ((P:ℝ)+1)⁻¹ := by
  unfold value
  rw [List.length_ofFn]
  exact (raw_error rho (precision rho m P) hrho hscale S u hu hc x).trans (precision_budget rho m P)

end ContinuumCoulomb.ManufacturedFieldEvaluation

end

end OAI
