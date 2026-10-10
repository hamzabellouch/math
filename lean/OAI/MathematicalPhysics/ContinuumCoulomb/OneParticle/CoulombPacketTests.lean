import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CoulombPackets

namespace OAI

/-! Finite packet combinations and the exact global Poisson duality for
smooth compact tests. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace ContinuumCoulomb.CoulombPacket

def zero : CoulombPacket where
  value _ := 0
  continuous := continuous_const
  integrable := integrable_zero Position ℝ volume
  bound := 0
  bound_nonnegative := le_rfl
  bound_spec _ := by simp

def sumList : List CoulombPacket → CoulombPacket
  | [] => zero
  | f :: fs => add f (sumList fs)

theorem pair_zero_left (f : CoulombPacket) : pair zero f = 0 := by
  simp [pair, zero]

theorem pair_sumList_left (fs : List CoulombPacket) (g : CoulombPacket) :
    pair (sumList fs) g = (fs.map (fun f => pair f g)).sum := by
  induction fs with
  | nil => exact pair_zero_left g
  | cons f fs ih => simp only [sumList, pair_add_left, ih, List.map_cons, List.sum_cons]

def combination {m : ℕ} (f : Fin m → CoulombPacket) (d : Fin m → ℝ) : CoulombPacket :=
  sumList (List.ofFn (fun i => smul (d i) (f i)))

theorem pair_combination_left {m : ℕ} (f : Fin m → CoulombPacket) (d : Fin m → ℝ)
    (g : CoulombPacket) : pair (combination f d) g = ∑ i, d i * pair (f i) g := by
  rw [combination, pair_sumList_left, List.map_ofFn, List.sum_ofFn]
  simp only [Function.comp_def, pair_smul_left]

theorem pair_combination_right {m : ℕ} (f : CoulombPacket) (g : Fin m → CoulombPacket)
    (d : Fin m → ℝ) : pair f (combination g d) = ∑ j, d j * pair f (g j) := by
  calc
    _ = pair (combination g d) f := pair_symmetric _ _
    _ = ∑ j, d j * pair (g j) f := pair_combination_left g d f
    _ = _ := Finset.sum_congr rfl (fun j _ => congrArg (fun a => d j * a) (pair_symmetric (g j) f))

theorem pair_combinations {m n : ℕ} (f : Fin m → CoulombPacket) (g : Fin n → CoulombPacket)
    (d : Fin m → ℝ) (e : Fin n → ℝ) :
    pair (combination f d) (combination g e) =
      ∑ i, ∑ j, d i * e j * pair (f i) (g j) := by
  rw [pair_combination_left]
  simp_rw [pair_combination_right, Finset.mul_sum, mul_assoc]

def ofCompact (f : Position → ℝ) (hf : Continuous f) (hc : HasCompactSupport f) : CoulombPacket where
  value := f
  continuous := hf
  integrable := hf.integrable_of_hasCompactSupport hc
  bound := max (Classical.choose (hc.exists_bound_of_continuous hf)) 0
  bound_nonnegative := le_max_right _ _
  bound_spec x := (Classical.choose_spec (hc.exists_bound_of_continuous hf) x).trans (le_max_left _ _)

def test (χ : Position → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) : CoulombPacket :=
  ofCompact (Coulomb.testCharge χ) (Coulomb.testCharge_continuous hχ) (Coulomb.testCharge_compact hc)

theorem pair_test (f : CoulombPacket) (χ : Position → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) :
    pair f (test χ hχ hc) = ∫ x, f x * χ x := by
  unfold pair
  rw [Measure.volume_eq_prod, integral_prod _ (joint_integrable f (test χ hχ hc))]
  apply integral_congr_ae
  filter_upwards [] with x
  change (∫ y, f x * Coulomb.testCharge χ y * Coulomb.coulombKernel (x - y)) = _
  rw [show (fun y => f x * Coulomb.testCharge χ y * Coulomb.coulombKernel (x - y)) =
      (fun y => f x * (Coulomb.coulombKernel (x - y) * Coulomb.testCharge χ y)) by funext y; ring,
    integral_const_mul, Coulomb.testCharge_potential hχ hc]

theorem test_pair_test (χ ψ : Position → ℝ) (hχ : ContDiff ℝ ∞ χ) (hψ : ContDiff ℝ ∞ ψ)
    (hcχ : HasCompactSupport χ) (hcψ : HasCompactSupport ψ) :
    pair (test χ hχ hcχ) (test ψ hψ hcψ) = ∫ x, Coulomb.testCharge χ x * ψ x :=
  pair_test _ _ hψ hcψ

theorem test_pair_orthogonal (χ ψ : Position → ℝ) (hχ : ContDiff ℝ ∞ χ) (hψ : ContDiff ℝ ∞ ψ)
    (hcχ : HasCompactSupport χ) (hcψ : HasCompactSupport ψ)
    (hd : Disjoint (tsupport χ) (tsupport ψ)) : pair (test χ hχ hcχ) (test ψ hψ hcψ) = 0 := by
  rw [test_pair_test]
  have hz (x : Position) : Coulomb.testCharge χ x * ψ x = 0 := by
    by_cases hx : x ∈ tsupport χ
    · rw [image_eq_zero_of_notMem_tsupport (fun hy => Set.disjoint_left.mp hd hx hy), mul_zero]
    · rw [Coulomb.testCharge_zero hx, zero_mul]
  simp_rw [hz, integral_zero]

end ContinuumCoulomb.CoulombPacket

end

end OAI
