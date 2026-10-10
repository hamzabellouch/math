import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanModel
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

namespace OAI

/-! # Primary decomposition from the triangular adjoint basis

The real triangular basis supplies the real generalized eigenspace
decomposition required by the Cartan root-space construction.
-/

noncomputable section

open scoped BigOperators

namespace PolycyclicRecognition

theorem prod_dvd_pow_card {R I : Type*} [CommMonoid R]
    (s : Finset I) (f : I → R) (a : R) (h : ∀ i ∈ s, f i ∣ a) :
    (∏ i ∈ s, f i) ∣ a ^ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.card_insert_of_notMem hi, pow_succ']
    exact mul_dvd_mul (h i (by simp)) (ih (fun j hj => h j (by simp [hj])))

/-- An annihilating product of real linear factors gives a decomposition
into generalized eigenspaces, including repeated eigenvalues. -/
theorem iSup_maxGenEigenspace_eq_top_of_annihilating_product
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (F : Module.End ℝ V) (S : Finset ℝ) (n : ℕ)
    (hzero : Polynomial.aeval F ((∏ a ∈ S, (Polynomial.X - Polynomial.C a)) ^ n) = 0) :
    (⨆ a : ℝ, F.maxGenEigenspace a) = ⊤ := by
  let g : ℝ → Module.End ℝ V := fun a => (F - a • 1) ^ n
  have hcomm (a b : ℝ) : Commute (g a) (g b) := by
    have ha : Commute (a • (1 : Module.End ℝ V)) (F - b • 1) := by
      simpa only [Algebra.algebraMap_eq_smul_one] using
        (Algebra.commute_algebraMap_left a (F - b • 1))
    have hb : Commute F (b • (1 : Module.End ℝ V)) := by
      simpa only [Algebra.algebraMap_eq_smul_one] using
        (Algebra.commute_algebraMap_right b F)
    exact ((Commute.sub_right (Commute.refl F) hb).sub_left ha).pow_pow _ _
  have hmap := Finset.map_noncommProd S (fun a => (Polynomial.X - Polynomial.C a) ^ n)
    (fun _ _ _ _ _ => Commute.all _ _) (Polynomial.aeval F).toRingHom
  change Polynomial.aeval F (S.noncommProd _ _) = S.noncommProd
    (fun a => Polynomial.aeval F ((Polynomial.X - Polynomial.C a) ^ n)) _ at hmap
  have hprod : S.noncommProd g (fun a _ b _ _ => hcomm a b) = 0 := by
    have he : Polynomial.aeval F ((∏ a ∈ S, (Polynomial.X - Polynomial.C a)) ^ n) =
        S.noncommProd g (fun a _ b _ _ => hcomm a b) := by
      simpa only [g, Finset.noncommProd_eq_prod, ← Finset.prod_pow, map_pow, map_sub,
        Polynomial.aeval_X, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one] using hmap
    exact he.symm.trans hzero
  have hind : S.SupIndep (fun a => LinearMap.ker (g a)) := by
    simpa only [g, ← Module.End.genEigenspace_nat] using
      (F.independent_genEigenspace (n : ℕ∞)).supIndep' S
  have hk := LinearMap.ker_noncommProd_eq_of_supIndep_ker S
    (fun a _ b _ _ => hcomm a b) hind
  rw [hprod, LinearMap.ker_zero] at hk
  apply top_unique
  rw [hk]
  apply iSup_le
  intro a
  apply iSup_le
  intro _
  rw [show LinearMap.ker (g a) = F.genEigenspace a (n : ℕ∞) by
    exact Module.End.genEigenspace_nat.symm]
  exact ((F.genEigenspace a).monotone le_top).trans (le_iSup F.maxGenEigenspace a)

namespace TriangularAdjoint

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : TriangularAdjoint L n)

/-- The real triangular adjoint basis implies real triangularizability
in the generalized-eigenspace sense used by the library's Cartan theory. -/
theorem isTriangularizable (T : TriangularAdjoint L n) :
    LieModule.IsTriangularizable ℝ L L where
  maxGenEigenspace_eq_top x := by
    classical
    let F := LieAlgebra.ad ℝ L x
    let d : Fin n → ℝ := fun i => T.character i x
    let S := Finset.univ.image d
    let Q : Polynomial ℝ := ∏ a ∈ S, (Polynomial.X - Polynomial.C a)
    have hdiv : F.charpoly ∣ Q ^ n := by
      rw [← LinearMap.charpoly_toMatrix F T.basis,
        Matrix.charpoly_of_isUpperTriangular _ (T.upper x)]
      have hh := prod_dvd_pow_card Finset.univ
        (fun i : Fin n => Polynomial.X - Polynomial.C (d i)) Q (by
          intro i _
          exact Finset.dvd_prod_of_mem _ (Finset.mem_image_of_mem d (Finset.mem_univ i)))
      simpa only [Finset.card_univ, Fintype.card_fin, d, character_eq_diag] using hh
    obtain ⟨q, hq⟩ := hdiv
    apply iSup_maxGenEigenspace_eq_top_of_annihilating_product F S n
    change Polynomial.aeval F (Q ^ n) = 0
    rw [hq, map_mul, F.aeval_self_charpoly, zero_mul]

end TriangularAdjoint

end PolycyclicRecognition

end

end OAI
