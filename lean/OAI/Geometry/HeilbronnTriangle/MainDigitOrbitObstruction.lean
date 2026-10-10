import OAI.Geometry.HeilbronnTriangle.MainDigitLaw
import OAI.Geometry.HeilbronnTriangle.MainDigitObstruction
import OAI.Geometry.HeilbronnTriangle.MainOrbitObstruction
import OAI.Geometry.HeilbronnTriangle.IntegerPointLawTriples

namespace OAI


noncomputable section

attribute [local irreducible] Problem355.heilbronnT Problem355.heilbronnM

namespace Problem355.MainDigitOrbitObstruction

open Parameters FiniteFieldLabels MainDigitLaw OrbitSampling

attribute [local instance] Classical.propDecidable

variable {r : ℕ} [Fact r.Prime]
variable (D : PrimeParameterData heilbronnK r)

def columns (h : ℕ) (labels : Fin 3 → Label r) (f : MainDigitLaw.Array r) :
    Fin 3 → Fin 3 → ZMod h :=
  fun j i => ((∑ v : Fin heilbronnK,
    (digit D (labels j) i v (f i j v)).val * D.B ^ v.val : ℕ) : ZMod h)

lemma columns_eq_matrix (labels : Fin 3 → Label r) (f : MainDigitLaw.Array r) :
    columns D (D.B ^ heilbronnK) labels f =
      Matrix.transpose (MainDigitLaw.matrix D labels f) := rfl

lemma columns_eq_latent (z : Fin 3 → MainDigitLaw.Latent r) :
    columns D (D.B ^ heilbronnK) (DigitColumnLaw.tripleEquiv z).1
      (DigitColumnLaw.tripleEquiv z).2 = (fun j => MainDigitLaw.column D (z j)) := rfl

theorem small_det_forces_repeated_labels (hr : 2 < r)
    (h : ℕ) [NeZero h] (hh : h = D.h)
    (labels : Fin 3 → Label r) (f : MainDigitLaw.Array r)
    (A : Matrix (Fin 3) (Fin 3) ℤ)
    (hA : MainOrbitObstruction.columnResidue h A ∈
      orbitFinset (MainGroup h) (columns D h labels f))
    (hsmall : |A.det| ≤ (D.tau : ℤ)) :
    ∃ i j : Fin 3, i ≠ j ∧ labels i = labels j := by
  obtain ⟨G, hG⟩ := MainOrbitObstruction.reduction_of_mem_orbit h
    (columns D h labels f) A hA
  exact MainDigitObstruction.finite_small_det_forces_repeated_labels hr D h hh labels
    (fun i j v => (digit D (labels j) i v (f i j v)).val)
    (fun i j v => digit_le D (labels j) i v (f i j v))
    (fun i j v => digit_residue D (labels j) i v (f i j v)) A G hG hsmall

theorem det_abs_gt_of_injective_labels (hr : 2 < r)
    (h : ℕ) [NeZero h] (hh : h = D.h)
    (labels : Fin 3 → Label r) (hinj : Function.Injective labels)
    (f : MainDigitLaw.Array r) (A : Matrix (Fin 3) (Fin 3) ℤ)
    (hA : MainOrbitObstruction.columnResidue h A ∈
      orbitFinset (MainGroup h) (columns D h labels f)) :
    (D.tau : ℤ) < |A.det| := by
  by_contra hn
  obtain ⟨i, j, hij, heq⟩ := small_det_forces_repeated_labels D hr h hh labels f A hA
    (le_of_not_gt hn)
  exact hij (hinj heq)

theorem lifted_small_event_eq_zero
    {X Ω Y : Type*} [DecidableEq X] [Fintype Ω]
    (hr : 2 < r) (h : ℕ) [NeZero h] (hh : h = D.h)
    (labels : Fin 3 → Label r) (hinj : Function.Injective labels)
    (f : MainDigitLaw.Array r)
    (A : X → Matrix (Fin 3) (Fin 3) ℤ) (g : X → Fin 3 → Y)
    (w : Ω → ℝ) (V : Ω → Finset Y) (s M : ℕ) (S : Finset X) :
    (∑ x ∈ S.filter (fun x => |(A x).det| ≤ (D.tau : ℤ)),
      LiftingProbability.liftedMass
        (fun x => MainOrbitObstruction.columnResidue h (A x)) g
        (orbitFinset (MainGroup h) (columns D h labels f)) w V s M x) = 0 := by
  apply LiftingProbability.lifted_small_event_eq_zero
  intro x _ hx
  exact det_abs_gt_of_injective_labels D hr h hh labels hinj f (A x) hx

theorem badDeterminant_mass_eq_zero {Ω : Type*} [Fintype Ω]
    (hr : 2 < r) (h : ℕ) [NeZero h] (hh : h = D.h)
    (labels : Fin 3 → Label r) (hinj : Function.Injective labels)
    (f : MainDigitLaw.Array r) (N q s M : ℕ)
    (w : Ω → ℝ) (V : Ω → Finset (Fin 3 → ZMod q)) :
    (∑ x ∈ (Finset.univ : Finset (Fin 3 → IntegerSampling.Box N 3
        (IntegerSampling.samplingShift N))).filter
          (IntegerPointLaw.badDeterminantEvent (D.tau : ℤ)),
      LiftingProbability.liftedMass
        (fun x i => IntegerSampling.residue h (x i))
        (fun x i => IntegerSampling.residue q (x i))
        (orbitFinset (MainGroup h) (columns D h labels f)) w V s M x) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro x hx
  have hsmall : |(integralMatrix x).det| ≤ (D.tau : ℤ) :=
    (Finset.mem_filter.mp hx).2.2.2.2
  have hnot : (fun i => IntegerSampling.residue h (x i)) ∉
      orbitFinset (MainGroup h) (columns D h labels f) := by
    intro hOrbit
    exact (not_lt_of_ge hsmall)
      (det_abs_gt_of_injective_labels D hr h hh labels hinj f (integralMatrix x) hOrbit)
  simp only [LiftingProbability.liftedMass, LiftingProbability.residueMass,
    LiftingProbability.mainMass, hnot, ite_false, zero_mul, zero_div]

end Problem355.MainDigitOrbitObstruction

end

end OAI
