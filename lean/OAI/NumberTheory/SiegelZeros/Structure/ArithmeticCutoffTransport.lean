import Mathlib.Data.Fintype.EquivFin
import OAI.NumberTheory.SiegelZeros.Characters.CharacterDeterminant
import OAI.NumberTheory.SiegelZeros.Determinants.RectangleDeterminant
import OAI.NumberTheory.SiegelZeros.Intersection.IsolatedBezoutFromRegularSelection
import OAI.NumberTheory.SiegelZeros.LocalAlgebra.HeightFourLength
import OAI.NumberTheory.SiegelZeros.LocalAlgebra.ResidueDirectionSelection
import OAI.NumberTheory.SiegelZeros.LocalAlgebra.ScalarExtension

namespace OAI

namespace SiegelZeros

section

noncomputable section
namespace WeightedTorusJets.W19

open MvPolynomial
open WeightedTorusJets.W18
open scoped BigOperators

section Support
variable {σ R : Type*} [CommSemiring R] [Fintype σ]

theorem support_iteratedInvariant_subset (v : σ → R) (a : ℕ)
    (F : MvPolynomial σ R) :
    (iteratedInvariant v a F).support ⊆ F.support := by
  induction a with
  | zero => exact fun _ h => h
  | succ a ha =>
      change ((fun G => invariantDerivation v G)^[a+1] F).support ⊆ F.support
      rw [Function.iterate_succ_apply']
      exact (support_invariantDerivation_subset v (iteratedInvariant v a F)).trans ha

theorem support_mixedInvariant_subset (v : Fin 3 → σ → R) (a : Fin 3 → ℕ)
    (F : MvPolynomial σ R) :
    (mixedInvariant v a F).support ⊆ F.support := by
  exact (support_iteratedInvariant_subset (v 0) (a 0) _).trans
    ((support_iteratedInvariant_subset (v 1) (a 1) _).trans
      (support_iteratedInvariant_subset (v 2) (a 2) F))

theorem mixedInvariant_totalDegree_le (v : Fin 3 → σ → R) (a : Fin 3 → ℕ)
    (F : MvPolynomial σ R) :
    (mixedInvariant v a F).totalDegree ≤ F.totalDegree :=
  MvPolynomial.totalDegree_le_of_support_subset (support_mixedInvariant_subset v a F)

theorem inBox_mixedInvariant (v : Fin 3 → σ → R) (a : Fin 3 → ℕ)
    {N : ℕ} {F : MvPolynomial σ R} (hF : InBox N F) :
    InBox N (mixedInvariant v a F) := by
  intro n hn i
  exact hF n (support_mixedInvariant_subset v a F hn) i

end Support

section FourVariables
variable {R : Type*} [CommSemiring R]

theorem totalDegree_le_of_inBox {N : ℕ} {F : MvPolynomial (Fin 4) R}
    (hF : InBox N F) : F.totalDegree ≤ 4 * N := by
  classical
  rw [MvPolynomial.totalDegree, Finset.sup_le_iff]
  intro n hn
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
  calc
    (∑ i : Fin 4, n i) ≤ ∑ _i : Fin 4, N :=
      Finset.sum_le_sum (fun i _ => Nat.le_of_lt (hF n hn i))
    _ = 4 * N := by simp

theorem mixedInvariant_totalDegree_le_of_inBox (v : Fin 3 → Fin 4 → R)
    (a : Fin 3 → ℕ) {N : ℕ} {F : MvPolynomial (Fin 4) R}
    (hF : InBox N F) : (mixedInvariant v a F).totalDegree ≤ 4 * N :=
  (mixedInvariant_totalDegree_le v a F).trans (totalDegree_le_of_inBox hF)

end FourVariables

section StrictDegree
variable {K : Type*} [Field K]

theorem mixedInvariant_totalDegree_lt_of_inBox (v : Fin 3 → Fin 4 → K)
    (a : Fin 3 → ℕ) {N : ℕ} (hN : 0 < N) {F : MvPolynomial (Fin 4) K}
    (hF : InBox N F) : (mixedInvariant v a F).totalDegree < 4 * N :=
  SiegelZeros.W17.totalDegree_lt K hN (inBox_mixedInvariant v a hF)

end StrictDegree
end WeightedTorusJets.W19

end

end

section

noncomputable section
namespace WeightedTorusJets.W28

open SiegelZeros.W58 SiegelZerosAwei.W21 SiegelZeros.W23
open ResidueDirectionBasis NormalExactness
open scoped BigOperators

@[reducible] local instance actualComponentHasQuotient
    (P : Ideal (TorusRing ℂ)) [P.IsPrime] :
    HasQuotient (Localization.AtPrime P) (Ideal (Localization.AtPrime P)) :=
  @Ideal.instHasQuotient (Localization.AtPrime P) inferInstance

attribute [local instance 2000] Monoid.toMulAction Semiring.toModule

def boundedDerivativePolynomial (v : Fin 3 → Fin 4 → ℂ)
    (F : AmbientPolynomial ℂ) (t : Fin 3 → ℕ) (b : ℕ)
    (a : {a : Fin 3 → ℕ // ∀ j, a j ≤ b * t j}) : AmbientPolynomial ℂ :=
  W19.mixedInvariant v a.val F

theorem derivativeIdeal_eq_map_boundedDerivative (v : Fin 3 → Fin 4 → ℂ)
    (F : AmbientPolynomial ℂ) (t : Fin 3 → ℕ) (b : ℕ) :
    derivativeIdeal v F t b =
      (Ideal.span (Set.range (boundedDerivativePolynomial v F t b))).map
        (algebraMap (AmbientPolynomial ℂ) (TorusRing ℂ)) := by
  rw [Ideal.map_span]
  unfold derivativeIdeal
  congr 1
  ext f
  constructor
  · rintro ⟨a, ha, hf⟩
    refine ⟨boundedDerivativePolynomial v F t b ⟨a, ha⟩, ⟨⟨a, ha⟩, rfl⟩, ?_⟩
    exact hf.symm
  · rintro ⟨p, ⟨a, rfl⟩, ha⟩
    exact ⟨a.val, a.property, ha.symm⟩

theorem source_vanishing_on_four_truncations
    (v : Fin 3 → Fin 4 → ℂ) {H N : ℕ} (hH : 0 < H) (hHN : H ≤ N)
    (F : AmbientPolynomial ℂ)
    (hvan : ∀ a : Fin 3 → ℕ,
      (a 0 : ℝ) ≤ 32 * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ) →
      (a 1 : ℝ) ≤ 32 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (4 / 3 : ℝ) →
      (a 2 : ℝ) ≤ 32 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (4 / 3 : ℝ) →
      MvPolynomial.eval (fun _ => (1 : ℂ)) (W19.mixedInvariant v a F) = 0) :
    ∀ a : Fin 3 → ℕ, (∀ j, a j ≤ 4 * RectangleNumerics.truncation H N j) →
      MvPolynomial.eval (fun _ => (1 : ℂ)) (W19.mixedInvariant v a F) = 0 := by
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have hNr : (0 : ℝ) < N := by exact_mod_cast (hH.trans_le hHN)
  intro a ha
  have hb (j : Fin 3) : (a j : ℝ) ≤ RectangleNumerics.width H N j := by
    have hcast : (a j : ℝ) ≤ 4 * (RectangleNumerics.truncation H N j : ℝ) := by
      exact_mod_cast ha j
    exact hcast.trans (RectangleNumerics.four_mul_truncation_le_width H N hHr hNr j)
  apply hvan a
  · simpa [RectangleNumerics.width] using hb 0
  · convert hb 1 using 1; norm_num [RectangleNumerics.width]
  · have htwo : (2 : Fin 3) ≠ 0 := by decide
    convert hb 2 using 1; norm_num [RectangleNumerics.width, htwo]

theorem original_hyperplane_basis_independent (c : Fin 4 → ℂ)
    (b : Module.Basis (Fin 3) ℂ (coefficientForm ℂ c).ker) :
    LinearIndependent ℂ (fun i => (b i).val) := by
  exact b.linearIndependent.map' (coefficientForm ℂ c).ker.subtype
    (Submodule.ker_subtype _)

theorem actual_positive_component_length_lower
    (c : Fin 4 → ℂ) (hc : LinearIndependent ℚ c)
    (basis : Module.Basis (Fin 3) ℂ (coefficientForm ℂ c).ker)
    (P : Ideal (TorusRing ℂ)) [P.IsPrime]
    (hPid : P ≤ identityIdeal ℂ) (h : ℕ) (hp : P.height = h) (hh : h ≤ 3)
    (F : AmbientPolynomial ℂ) (t : Fin 3 → ℕ) (b : ℕ)
    (hP : derivativeIdeal (fun i => (basis i).val) F t (b + 1) ≤ P) :
    ∃ S : Set (Fin 3), Nat.card S = h ∧
      (∏ j, (selectedCutoffs t S j + 1) : ℕ) ≤
        Module.length (Localization.AtPrime P)
          (Localization.AtPrime P ⧸
            (derivativeIdeal (fun i => (basis i).val) F t b).map
              (algebraMap (TorusRing ℂ) (Localization.AtPrime P))) := by
  have hc0 : c ≠ 0 := by
    intro hz
    exact hc.ne_zero 0 (congrFun hz 0)
  have hp3 : P.height ≤ 3 := by
    rw [hp]
    exact_mod_cast hh
  have hω := SiegelZerosAwei.Workers.W14.torus_residueLogForm_ne_zero_unconditional
    P hPid hp3 hc
  obtain ⟨S, hcard, _, hsurj⟩ :=
    original_basis_selected_normals ℂ P h hp c hc0 hω basis
  exact ⟨S, hcard,
    W24.selected_component_length_lower ℂ (fun i => (basis i).val) F t S b P hP hsurj⟩

theorem actual_component_length_lower
    (c : Fin 4 → ℂ) (hc : LinearIndependent ℚ c)
    (basis : Module.Basis (Fin 3) ℂ (coefficientForm ℂ c).ker)
    (P : Ideal (TorusRing ℂ)) [P.IsPrime]
    (hPid : P ≤ identityIdeal ℂ) (h : ℕ) (hp : P.height = h) (hh : h ≤ 4)
    (F : AmbientPolynomial ℂ) (t : Fin 3 → ℕ) (b : ℕ)
    (hP : derivativeIdeal (fun i => (basis i).val) F t (b + 1) ≤ P) :
    ∃ S : Set (Fin 3), Nat.card S = min h 3 ∧
      (∏ j, (selectedCutoffs t S j + 1) : ℕ) ≤
        Module.length (Localization.AtPrime P)
          (Localization.AtPrime P ⧸
            (derivativeIdeal (fun i => (basis i).val) F t b).map
              (algebraMap (TorusRing ℂ) (Localization.AtPrime P))) := by
  by_cases hh3 : h ≤ 3
  · obtain ⟨S, hcard, hlower⟩ :=
      actual_positive_component_length_lower c hc basis P hPid h hp hh3 F t b hP
    exact ⟨S, hcard.trans (Nat.min_eq_left hh3).symm, hlower⟩
  · have hh4 : h = 4 := by omega
    subst h
    refine ⟨Set.univ, by simp, ?_⟩
    have hlower := height_four_component_length_lower P hPid hp
      (fun i => (basis i).val) (original_hyperplane_basis_independent c basis) F t b hP
    simpa only [selectedCutoffs, Set.mem_univ, ↓reduceIte] using hlower

theorem derivative_component_height_bounds
    (v : Fin 3 → Fin 4 → ℂ) (F : AmbientPolynomial ℂ) (hF : F ≠ 0)
    (t : Fin 3 → ℕ) (b : ℕ) (P : Ideal (TorusRing ℂ)) [P.IsPrime]
    (hmin : P ∈ (derivativeIdeal v F t b).minimalPrimes) :
    1 ≤ P.height.toNat ∧ P.height.toNat ≤ 4 ∧
      P.height = (P.height.toNat : ℕ∞) := by
  let : IsDomain (TorusRing ℂ) := SiegelZeros.W17.torus_isDomain ℂ
  have hP4 : P.height ≤ 4 := by
    have hh := (ringKrullDim_le_iff_height_le 4).mp (torus_dimension_le_four ℂ)
      (inferInstance : P.IsPrime)
    exact WithBot.coe_le_coe.mp hh
  have hPne : P ≠ ⊥ := by
    intro hz
    have hmem := hmin.1.2 (polynomial_mem_derivativeIdeal v F t b)
    rw [hz, Ideal.mem_bot] at hmem
    exact SiegelZeros.W17.polynomial_to_torus_ne_zero ℂ hF hmem
  have hpos := prime_height_toNat_succ_le (P := (⊥ : Ideal (TorusRing ℂ)))
    (by simp) hP4 (lt_of_le_of_ne bot_le hPne.symm)
  have hfin : P.height ≠ ⊤ := (lt_of_le_of_lt hP4 (ENat.natCast_lt_top 4)).ne
  refine ⟨?_, ENat.toNat_le_of_le_natCast hP4, (ENat.natCast_toNat hfin).symm⟩
  simpa only [Ideal.height_bot, ENat.toNat_zero, Nat.zero_add] using hpos

theorem exists_actual_component_with_length_lower
    (c : Fin 4 → ℂ) (hc : LinearIndependent ℚ c)
    (basis : Module.Basis (Fin 3) ℂ (coefficientForm ℂ c).ker)
    (F : AmbientPolynomial ℂ) (hF : F ≠ 0) (t : Fin 3 → ℕ)
    (hvanish : ∀ a : Fin 3 → ℕ, (∀ j, a j ≤ 4 * t j) →
      MvPolynomial.eval (fun _ : Fin 4 => (1 : ℂ))
        (W19.mixedInvariant (fun i => (basis i).val) a F) = 0) :
    ∃ b, b < 4 ∧ ∃ P : PrimeSpectrum (TorusRing ℂ),
      P.asIdeal ≤ identityIdeal ℂ ∧
      P.asIdeal ∈ (derivativeIdeal (fun i => (basis i).val) F t b).minimalPrimes ∧
      1 ≤ P.asIdeal.height.toNat ∧ P.asIdeal.height.toNat ≤ 4 ∧
      P.asIdeal.height = (P.asIdeal.height.toNat : ℕ∞) ∧
      ∃ S : Set (Fin 3), Nat.card S = min P.asIdeal.height.toNat 3 ∧
        (∏ j, (selectedCutoffs t S j + 1) : ℕ) ≤
          Module.length (Localization.AtPrime P.asIdeal)
            (Localization.AtPrime P.asIdeal ⧸
              (derivativeIdeal (fun i => (basis i).val) F t b).map
                (algebraMap (TorusRing ℂ) (Localization.AtPrime P.asIdeal))) := by
  obtain ⟨b, hb, P, hPid, hmin, hnext, _⟩ :=
    derivativeIdeals_common_component (fun i => (basis i).val) F t hF hvanish
  obtain ⟨hpos, hfour, hheight⟩ :=
    derivative_component_height_bounds (fun i => (basis i).val) F hF t b P.asIdeal hmin
  refine ⟨b, hb, P, hPid, hmin, hpos, hfour, hheight, ?_⟩
  exact actual_component_length_lower c hc basis P.asIdeal hPid _ hheight hfour
    F t b hnext.1.2

theorem actual_derivative_component_length_upper
    (hBezout : W22.LocalIsolatedBezoutStatement ℂ)
    (v : Fin 3 → Fin 4 → ℂ) {N : ℕ} (hN : 0 < N)
    (F : AmbientPolynomial ℂ) (hF : W18.InBox N F) (t : Fin 3 → ℕ) (b : ℕ)
    (P : Ideal (TorusRing ℂ)) [P.IsPrime]
    (h : ℕ) (hh1 : 1 ≤ h) (hh4 : h ≤ 4) (hheight : P.height = h)
    (hminimal : P ∈ (derivativeIdeal v F t b).minimalPrimes) :
    Module.length (Localization.AtPrime P)
      (Localization.AtPrime P ⧸ (derivativeIdeal v F t b).map
        (algebraMap (TorusRing ℂ) (Localization.AtPrime P))) ≤
      (((4 * N) ^ h : ℕ) : ℕ∞) := by
  rw [derivativeIdeal_eq_map_boundedDerivative] at hminimal ⊢
  apply torus_local_length_le_of_local_isolated_bezout hBezout
    (boundedDerivativePolynomial v F t b) (4 * N) h
  · intro a
    exact W19.mixedInvariant_totalDegree_le_of_inBox v a.val hF
  · omega
  · exact hh1
  · exact hh4
  · exact hminimal
  · exact hheight

theorem actual_rectangularAssertion_of_localBezout
    (hBezout : W22.LocalIsolatedBezoutStatement ℂ)
    (c : Fin 4 → ℂ) (hc : LinearIndependent ℚ c)
    (basis : Module.Basis (Fin 3) ℂ (coefficientForm ℂ c).ker)
    {H N : ℕ} (hH : 0 < H) (hHN : H ≤ N) :
    RectangularAssertion (fun i => (basis i).val) H N := by
  intro F hF hvan
  by_contra hFne
  let t : Fin 3 → ℕ := fun j => RectangleNumerics.truncation H N j
  have hvan4 := source_vanishing_on_four_truncations
    (fun i => (basis i).val) hH hHN F hvan
  obtain ⟨b, _hb, P, _hPid, hminimal, hh1, hh4, hheight, S, hcard, hlower⟩ :=
    exists_actual_component_with_length_lower c hc basis F hFne t hvan4
  have hupper := actual_derivative_component_length_upper hBezout
    (fun i => (basis i).val) (hH.trans_le hHN) F hF t b P.asIdeal
    P.asIdeal.height.toNat hh1 hh4 hheight hminimal
  exact RectangleNumerics.selectedCutoffs_length_bounds_incompatible H N
    P.asIdeal.height.toNat hH hHN hh1 hh4 S hcard _ hupper hlower

theorem actual_cutoff_spanning_of_localBezout
    (hBezout : W22.LocalIsolatedBezoutStatement ℂ)
    (c : Fin 4 → ℂ) (hc : LinearIndependent ℚ c)
    (basis : Module.Basis (Fin 3) ℂ (coefficientForm ℂ c).ker)
    {H N : ℕ} (hH : 0 < H) (hHN : H ≤ N) :
    W29.rowSpan (K := ℂ) (sourceRow (fun i => (basis i).val) H N)
      (W62.cutoff H (sourceCutoff H N)) = ⊤ :=
  cutoff_span_of_rectangularAssertion (fun i => (basis i).val) hH
    (actual_rectangularAssertion_of_localBezout hBezout c hc basis hH hHN)

theorem actual_selected_determinant_of_localBezout
    (hBezout : W22.LocalIsolatedBezoutStatement ℂ)
    (c : Fin 4 → ℂ) (hc : LinearIndependent ℚ c)
    (basis : Module.Basis (Fin 3) ℂ (coefficientForm ℂ c).ker)
    {H N : ℕ} (hH : 0 < H) (hHN : H ≤ N) :
    ∃ e : MonomialBox N ≃ W62.selected (K := ℂ) H (sourceCutoff H N)
      (sourceRow (fun i => (basis i).val) H N),
      Matrix.det (fun i j => sourceRow (fun i => (basis i).val) H N (e i) j) ≠ 0 :=
  selected_det_of_rectangularAssertion (fun i => (basis i).val) hH
    (actual_rectangularAssertion_of_localBezout hBezout c hc basis hH hHN)

end WeightedTorusJets.W28

end

end

section

noncomputable section

open scoped NumberField

namespace SiegelZerosAwei.W50

open WeightedTorusJets

def boxEnumeration (N : ℕ) : Fin (N ^ 4) ≃ W28.MonomialBox N :=
  (Fintype.equivFinOfCardEq (by simp [W28.MonomialBox])).symm

def boxExponents (N : ℕ) : Fin (N ^ 4) → Fin 4 →₀ ℕ :=
  fun i => W28.boxExponent (boxEnumeration N i)

theorem boxExponents_injective (N : ℕ) : Function.Injective (boxExponents N) :=
  (W28.boxExponent_injective N).comp (boxEnumeration N).injective

theorem boxExponents_lt (N : ℕ) (j : Fin (N ^ 4)) (i : Fin 4) :
    boxExponents N j i < N := by
  change (boxEnumeration N j i).val < N
  exact (boxEnumeration N j i).isLt

def sourceCutoff (H N : ℕ) : ℕ :=
  ⌊96 * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ)⌋₊

theorem sourceCutoff_le (H N : ℕ) :
    (sourceCutoff H N : ℝ) ≤
      96 * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ) := by
  unfold sourceCutoff
  exact Nat.floor_le (by positivity)

def ActualCutoffSpanning (H N : ℕ) (d : ℤ) (a : ℂ) (ha : a ^ 2 = (d : ℂ)) : Prop :=
  let L := SiegelZeros.W10.rootField a W60.sqrtTwo
  let f := algebraMap (𝓞 L) L
  let u := W37.integralRootA a W60.sqrtTwo d ha W60.sqrtTwo_sq
  let v := W37.integralRootB a W60.sqrtTwo d ha W60.sqrtTwo_sq
  let n : Fin (N ^ 4) → Fin 4 → ℤ := fun j i => (boxExponents N j i : ℤ)
  W29.rowSpan (K := L)
    (W60.weightedRow f (fun j => Awei.W39.theta u v (n j))
      (fun j => Awei.W39.theta (-u) v (n j))
      (fun j => Awei.W39.theta (-u) (-v) (n j)))
    (W62.cutoff H (sourceCutoff H N)) = ⊤

end SiegelZerosAwei.W50

end

end

section

noncomputable section
open scoped BigOperators NumberField
namespace WeightedTorusJets.W28

open SiegelZerosAwei

theorem rowSpan_top_of_field_map {K L ι n : Type*} [Field K] [Field L]
    [Fintype n] [DecidableEq ι] (f : K →+* L) (row : ι → n → K) (s : Finset ι)
    (hspan : W29.rowSpan (K := L) (fun i j => f (row i j)) s = ⊤) :
    W29.rowSpan (K := K) row s = ⊤ := by
  classical
  apply Submodule.eq_top_of_finrank_eq
  change Module.finrank K (Submodule.span K (row '' (s : Set ι))) = _
  rw [Set.image_eq_range]
  have hh : Submodule.span L (Set.range (fun (i : s) j => f (row i j))) = ⊤ := by
    unfold W29.rowSpan at hspan
    rw [Set.image_eq_range] at hspan
    exact hspan
  calc
    Module.finrank K (Submodule.span K (Set.range (fun i : s => row i))) =
        Module.finrank L (Submodule.span L (Set.range (fun (i : s) j => f (row i j)))) :=
      (W30.finrank_span_coordinateMap f (fun i : s => row i)).symm
    _ = Module.finrank L (n → L) := by rw [hh, finrank_top]
    _ = Module.finrank K (n → K) := by simp only [Module.finrank_pi]

theorem rowSpan_top_reindex {K ι m n : Type*} [Field K] [DecidableEq ι]
    (e : m ≃ n) (row : ι → n → K) (s : Finset ι)
    (hspan : W29.rowSpan (K := K) row s = ⊤) :
    W29.rowSpan (K := K) (fun i j => row i (e j)) s = ⊤ := by
  let E := LinearEquiv.funCongrLeft K K e
  have hm : (W29.rowSpan (K := K) row s).map E.toLinearMap =
      W29.rowSpan (K := K) (fun i j => row i (e j)) s := by
    simp only [W29.rowSpan, Submodule.map_span, Set.image_image]
    rfl
  rw [hspan, Submodule.map_top,
    LinearMap.range_eq_top.mpr E.surjective] at hm
  exact hm.symm

theorem actual_omega_independent (d : ℤ) (hd : Squarefree d)
    (hd1 : d ≠ 1) (hd2 : d ≠ 2) (a : ℂ) (ha : a ^ 2 = (d : ℂ)) :
    LinearIndependent ℚ (W13.omegaCoefficients a W60.sqrtTwo) := by
  have ha0 : a ≠ 0 := by
    intro hz
    have hd0 : (d : ℂ) = 0 := by simpa [hz] using ha.symm
    exact hd.ne_zero (by exact_mod_cast hd0)
  have hb0 : W60.sqrtTwo ≠ 0 := by
    intro hz
    have hb := W60.sqrtTwo_sq
    norm_num [hz] at hb
  apply W13.rationalIndependent_omegaCoefficients ha0 hb0
  exact SiegelZeros.W10.generators_linearIndependent_squarefree a W60.sqrtTwo
    d hd hd1 hd2 ha W60.sqrtTwo_sq

theorem actual_complex_cutoff_spanning
    (hBezout : W22.LocalIsolatedBezoutStatement ℂ)
    (H N : ℕ) (hH : 0 < H) (hHN : H ≤ N)
    (d : ℤ) (hd : Squarefree d) (hd1 : d ≠ 1) (hd2 : d ≠ 2)
    (a : ℂ) (ha : a ^ 2 = (d : ℂ)) :
    W29.rowSpan (K := ℂ) (sourceRow (W12.directions a W60.sqrtTwo) H N)
      (W62.cutoff H (sourceCutoff H N)) = ⊤ := by
  have ha0 : a ≠ 0 := by
    intro hz
    have hd0 : (d : ℂ) = 0 := by simpa [hz] using ha.symm
    exact hd.ne_zero (by exact_mod_cast hd0)
  have hb0 : W60.sqrtTwo ≠ 0 := by
    intro hz
    have hb := W60.sqrtTwo_sq
    norm_num [hz] at hb
  have hspan := actual_cutoff_spanning_of_localBezout hBezout
    (W13.omegaCoefficients a W60.sqrtTwo) (actual_omega_independent d hd hd1 hd2 a ha)
    (ResidueDirectionBasis.biquadraticCoordinateBasis ℂ a W60.sqrtTwo ha0 hb0) hH hHN
  simpa only [ResidueDirectionBasis.biquadraticCoordinateBasis_apply] using hspan

theorem map_theta_eigenvalue {R : Type*} [CommRing R] (f : R →+* ℂ)
    (u v : R) (n : Fin 4 →₀ ℕ) :
    f (Awei.W39.theta u v (fun i => (n i : ℤ))) =
      W18.eigenvalue ![1, f u, f v, f u * f v] n := by
  simp [Awei.W39.theta, W18.eigenvalue, Fin.sum_univ_succ]
  ring

theorem arithmeticRow_map_eq_sourceRow
    (H N : ℕ) (d : ℤ) (a : ℂ) (ha : a ^ 2 = (d : ℂ))
    (r : W62.Index H) (j : Fin (N ^ 4)) :
    let L := SiegelZeros.W10.rootField a W60.sqrtTwo
    let f := algebraMap (𝓞 L) L
    let u := W37.integralRootA a W60.sqrtTwo d ha W60.sqrtTwo_sq
    let v := W37.integralRootB a W60.sqrtTwo d ha W60.sqrtTwo_sq
    let n : Fin (N ^ 4) → Fin 4 → ℤ := fun j i => (W50.boxExponents N j i : ℤ)
    (SiegelZeros.W10.rootField a W60.sqrtTwo).val
      (W60.weightedRow f (fun j => Awei.W39.theta u v (n j))
        (fun j => Awei.W39.theta (-u) v (n j))
        (fun j => Awei.W39.theta (-u) (-v) (n j)) r j) =
      sourceRow (W12.directions a W60.sqrtTwo) H N r (W50.boxEnumeration N j) := by
  dsimp only
  let L := SiegelZeros.W10.rootField a W60.sqrtTwo
  let f : 𝓞 L →+* ℂ := (SiegelZeros.W10.rootField a W60.sqrtTwo).val.toRingHom.comp
    (algebraMap (𝓞 L) L)
  let u := W37.integralRootA a W60.sqrtTwo d ha W60.sqrtTwo_sq
  let v := W37.integralRootB a W60.sqrtTwo d ha W60.sqrtTwo_sq
  have hu : f u = a := rfl
  have hv : f v = W60.sqrtTwo := rfl
  have h0 := map_theta_eigenvalue f u v (W50.boxExponents N j)
  have h1 := map_theta_eigenvalue f (-u) v (W50.boxExponents N j)
  have h2 := map_theta_eigenvalue f (-u) (-v) (W50.boxExponents N j)
  simp only [map_neg, hu, hv, neg_mul] at h0 h1 h2
  simp only [W60.weightedRow, W40.rowEntry, map_mul, map_pow]
  change f (Awei.W39.theta u v (fun i => (W50.boxExponents N j i : ℤ))) ^ r.coords 0 *
      f (Awei.W39.theta (-u) v (fun i => (W50.boxExponents N j i : ℤ))) ^ r.coords 1 *
      f (Awei.W39.theta (-u) (-v) (fun i => (W50.boxExponents N j i : ℤ))) ^ r.coords 2 = _
  rw [h0, h1, h2]
  simp [sourceRow, W50.boxExponents, W12.directions, mul_neg]

theorem actualCutoffSpanning_of_localBezout
    (hBezout : W22.LocalIsolatedBezoutStatement ℂ)
    (H N : ℕ) (hH : 0 < H) (hHN : H ≤ N)
    (d : ℤ) (hd : Squarefree d) (hd1 : d ≠ 1) (hd2 : d ≠ 2)
    (a : ℂ) (ha : a ^ 2 = (d : ℂ)) :
    W50.ActualCutoffSpanning H N d a ha := by
  let L := SiegelZeros.W10.rootField a W60.sqrtTwo
  let f := algebraMap (𝓞 L) L
  let u := W37.integralRootA a W60.sqrtTwo d ha W60.sqrtTwo_sq
  let v := W37.integralRootB a W60.sqrtTwo d ha W60.sqrtTwo_sq
  let n : Fin (N ^ 4) → Fin 4 → ℤ := fun j i => (W50.boxExponents N j i : ℤ)
  let row := W60.weightedRow f (fun j => Awei.W39.theta u v (n j))
    (fun j => Awei.W39.theta (-u) v (n j))
    (fun j => Awei.W39.theta (-u) (-v) (n j)) (H := H)
  change W29.rowSpan (K := L) row (W62.cutoff H (W50.sourceCutoff H N)) = ⊤
  apply rowSpan_top_of_field_map (SiegelZeros.W10.rootField a W60.sqrtTwo).val.toRingHom
  have hs := rowSpan_top_reindex (W50.boxEnumeration N)
    (sourceRow (W12.directions a W60.sqrtTwo) H N)
    (W62.cutoff H (sourceCutoff H N))
    (actual_complex_cutoff_spanning hBezout H N hH hHN d hd hd1 hd2 a ha)
  have hrow : (fun i j => (SiegelZeros.W10.rootField a W60.sqrtTwo).val.toRingHom (row i j)) =
      (fun i j => sourceRow (W12.directions a W60.sqrtTwo) H N i
        (W50.boxEnumeration N j)) := by
    funext i j
    exact arithmeticRow_map_eq_sourceRow H N d a ha i j
  rw [hrow]
  exact hs

end WeightedTorusJets.W28

end

end

end SiegelZeros

end OAI
