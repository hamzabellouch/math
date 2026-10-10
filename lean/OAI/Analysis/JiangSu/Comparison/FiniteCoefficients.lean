import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.CentralSequences.FiniteCentral

namespace OAI

noncomputable section
namespace DirectComparison
open Pureness CurrentMain DirectPacking Filter
open scoped ComplexOrder

section Norms
variable {E S : Type*} [CStarAlgebra E] [PartialOrder E] [StarOrderedRing E]
variable (σ : S → TracialState E) [Nonempty S]
lemma familyTwoNorm_fintype_sum_le {J : Type*} [Fintype J] (f : J → E) :
    familyTwoNorm σ (∑ j, f j) ≤ ∑ j, familyTwoNorm σ (f j) := by
  apply ciSup_le
  intro s
  exact (traceTwoNorm_sum_le Finset.univ (σ s) f).trans
    (Finset.sum_le_sum fun j _ => traceTwoNorm_le_family σ s (f j))
lemma familyTraceNorm_fintype_sum_le {J : Type*} [Fintype J] (f : J → E) :
    familyTraceNorm σ (∑ j, f j) ≤ ∑ j, familyTraceNorm σ (f j) := by
  apply ciSup_le
  intro s
  rw [map_sum]
  exact (norm_sum_le _ _).trans
    (Finset.sum_le_sum fun j _ => traceNorm_le_family σ s (f j))
lemma familyTraceNorm_smul_le (c : ℂ) (a : E) :
    familyTraceNorm σ (c • a) ≤ ‖c‖*familyTraceNorm σ a := by
  apply ciSup_le
  intro s
  rw [map_smul,smul_eq_mul,norm_mul]
  exact mul_le_mul_of_nonneg_left (traceNorm_le_family σ s a) (norm_nonneg c)
end Norms
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [Nontrivial A] [Nonempty (TracialState A)]
variable (U : Ultrafilter ℕ) (hfree : (U : Filter ℕ) ≤ atTop)
variable (hsimple : TopologicallySimple A) (hinf : ¬FiniteDimensional ℂ A)
variable (hcmp : StrictComparison A) (hnuc : IsNuclear A)
local notation "D" => FamilyUltrapower (fun τ : TracialState A => τ) U
local notation "Λ" => familyLimitTrace (fun τ : TracialState A => τ) U
local notation "ι" => familyUltrapowerMap (fun τ : TracialState A => τ) U

include hfree hsimple hinf hcmp hnuc in

theorem comparison_finite_coefficients (F : Finset A) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : D, IsStarProjection p ∧ ∀ a ∈ F,
      familyTwoNorm Λ (p*ι a-ι a*p) < ε ∧
      familyTraceNorm Λ (p*ι a-(1/2:ℂ) • ι a) < ε := by
  classical
  choose u c he hc using fun a : A => CStarAlgebra.exists_sum_four_unitary a
  let K := F.biUnion fun a => Finset.univ.image (u a)
  let R := 1+∑ a ∈ F, ‖a‖
  have hR : 0 < R := by dsimp [R]; positivity
  have hRa {a : A} (ha : a ∈ F) : ‖a‖ ≤ R := by
    have h := Finset.single_le_sum (fun a (_ : a ∈ F) => norm_nonneg a) ha
    dsimp [R]
    linarith
  let δ := ε/(4*R)
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨p,hp,ht⟩ := comparison_finite_central_splitting U hfree hsimple hinf hcmp hnuc K hδ
  refine ⟨p,hp,?_⟩
  intro a ha
  have hmem (j : Fin 4) : u a j ∈ K :=
    Finset.mem_biUnion.mpr ⟨a,ha,Finset.mem_image_of_mem _ (Finset.mem_univ j)⟩
  have hnum : (∑ j : Fin 4, (‖a‖/2)*δ) < ε := by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    have hle : 4*(‖a‖/2)*δ ≤ 2*R*δ := by nlinarith [mul_le_mul_of_nonneg_right (hRa ha) hδ.le]
    have hid : 2*R*δ = ε/2 := by dsimp [δ]; field_simp; ring
    calc
      _ = 4*(‖a‖/2)*δ := by ring
      _ ≤ 2*R*δ := hle
      _ = ε/2 := hid
      _ < ε := by linarith
  have hcomm : p*ι a-ι a*p = ∑ j, c a j • (p*ι (u a j:A)-ι (u a j:A)*p) := by
    conv_lhs => rw [he a]
    rw [map_sum,Finset.mul_sum,Finset.sum_mul,←Finset.sum_sub_distrib]
    simp only [map_smul,mul_smul_comm,smul_mul_assoc,smul_sub]
  have hhalf : p*ι a-(1/2:ℂ) • ι a =
      ∑ j, c a j • (p*ι (u a j:A)-(1/2:ℂ) • ι (u a j:A)) := by
    conv_lhs => rw [he a]
    rw [map_sum,Finset.mul_sum,Finset.smul_sum,←Finset.sum_sub_distrib]
    simp only [map_smul,mul_smul_comm,smul_sub,smul_comm (1/2:ℂ)]
  constructor
  · rw [hcomm]
    apply lt_of_le_of_lt ((familyTwoNorm_fintype_sum_le Λ _).trans ?_) hnum
    apply Finset.sum_le_sum
    intro j _
    exact (familyTwoNorm_smul_le Λ _ _).trans (mul_le_mul (hc a j)
      (ht (u a j) (hmem j)).1.le (familyTwoNorm_nonneg Λ _) (by positivity))
  · rw [hhalf]
    apply lt_of_le_of_lt ((familyTraceNorm_fintype_sum_le Λ _).trans ?_) hnum
    apply Finset.sum_le_sum
    intro j _
    exact (familyTraceNorm_smul_le Λ _ _).trans (mul_le_mul (hc a j)
      (ht (u a j) (hmem j)).2.le (familyTraceNorm_nonneg Λ _) (by positivity))

include hfree hsimple hinf hcmp hnuc in

theorem comparison_coordinate_halving (F : Finset A) {ε : ℝ} (hε : 0 < ε) :
    ∃ b : A, IsSelfAdjoint b ∧ ‖b‖ ≤ 2 ∧
      familyTwoNorm (fun τ : TracialState A => τ) (b*b-b) < ε ∧ ∀ a ∈ F,
      familyTwoNorm (fun τ : TracialState A => τ) (b*a-a*b) < ε ∧
      familyTraceNorm (fun τ : TracialState A => τ) (b*a-(1/2:ℂ) • a) < ε := by
  obtain ⟨p,hp,ht⟩ := comparison_finite_coefficients U hfree hsimple hinf hcmp hnuc F hε
  exact exists_coordinate_split (fun τ : TracialState A => τ) U F hε hp
    (fun a ha => (ht a ha).1) (fun a ha => (ht a ha).2)

end DirectComparison

namespace DirectComparison
open Pureness CurrentMain Filter
open scoped Topology ComplexOrder ENNReal NNReal

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [Nontrivial A] [Nonempty (TracialState A)]
variable (U : Ultrafilter ℕ) (hfree : (U : Filter ℕ) ≤ atTop)
variable (hsimple : TopologicallySimple A) (hinf : ¬FiniteDimensional ℂ A)
variable (hcmp : StrictComparison A) (hnuc : IsNuclear A)
local notation "τ" => (fun t : TracialState A => t)
local notation "D" => FamilyUltrapower τ U
local notation "Λ" => familyLimitTrace τ U
include hfree hsimple hinf hcmp hnuc in
theorem comparison_relative_halving (x : ℕ → D) :
    ∃ p : D, IsStarProjection p ∧ ∀ k : ℕ,
      p*x k=x k*p ∧ ∀ s : ℕ → TracialState A,
        (Λ s).functional (p*x k)=(1/2:ℂ)*(Λ s).functional (x k) := by
  classical
  let J := familyNullIdeal τ (U : Filter ℕ)
  choose a ha using fun k => J.quotientMap_surjective (x k)
  let e : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have he (n : ℕ) : 0 < e n := by dsimp [e]; positivity
  have helim : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hb (n : ℕ) : ∃ b : A, IsSelfAdjoint b ∧ ‖b‖ ≤ 2 ∧
      familyTwoNorm τ (b*b-b) < e n ∧ ∀ k ≤ n,
      familyTwoNorm τ (b*a k n-a k n*b) < e n ∧
      familyTraceNorm τ (b*a k n-(1/2:ℂ) • a k n) < e n := by
    obtain ⟨b,hb1,hb2,hb3,hb4⟩ := comparison_coordinate_halving U hfree
      hsimple hinf hcmp hnuc ((Finset.range (n+1)).image (fun k => a k n)) (he n)
    refine ⟨b,hb1,hb2,hb3,fun k hk => hb4 (a k n) ?_⟩
    exact Finset.mem_image.mpr ⟨k,Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hk),rfl⟩
  choose b hbsa hbn hbd hbt using hb
  let c : lp (fun _ : ℕ => A) ∞ :=
    ⟨b,memℓp_infty_iff.mpr ⟨2,by rintro _ ⟨n,rfl⟩; exact hbn n⟩⟩
  have hd : IsFamilyNull τ (U : Filter ℕ) (fun n => c n*c n-c n) := by
    exact (squeeze_zero (fun _ => familyTwoNorm_nonneg τ _)
      (fun n => (hbd n).le) helim).mono_left hfree
  refine ⟨J.quotientMap c,projection_of_bounded_sequence τ U c hbsa hd,?_⟩
  intro k
  constructor
  · have hc : IsFamilyNull τ (U : Filter ℕ) (fun n => (c*a k-a k*c) n) := by
      apply Tendsto.mono_left _ hfree
      apply squeeze_zero' (Eventually.of_forall (fun _ => familyTwoNorm_nonneg τ _)) _ helim
      filter_upwards [eventually_ge_atTop k] with n hn
      exact (hbt n k hn).1.le
    have hz := (familyQuotientMap_eq_zero τ U (c*a k-a k*c)).mpr hc
    rwa [map_sub,map_mul,map_mul,ha k,sub_eq_zero] at hz
  · intro s
    have ht : Tendsto (fun n => familyTraceNorm τ ((c*a k-(1/2:ℂ) • a k) n))
        (U : Filter ℕ) (𝓝 0) := by
      apply Tendsto.mono_left _ hfree
      apply squeeze_zero' (Eventually.of_forall (fun _ => familyTraceNorm_nonneg τ _)) _ helim
      filter_upwards [eventually_ge_atTop k] with n hn
      exact (hbt n k hn).2.le
    have hz := tendsto_nhds_unique (familyTraceNorm_limitTrace_tendsto τ U (c*a k-(1/2:ℂ) • a k)) ht
    have hs : (Λ s).functional (J.quotientMap (c*a k-(1/2:ℂ) • a k))=0 :=
      norm_eq_zero.mp (le_antisymm ((traceNorm_le_family Λ s _).trans hz.le) (norm_nonneg _))
    simpa only [map_sub,map_mul,map_smul,ha k,smul_eq_mul,sub_eq_zero] using hs

end DirectComparison

namespace DirectComparison
open Pureness CurrentMain Filter
open scoped Topology ComplexOrder

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [Nontrivial A] [Nonempty (TracialState A)]
variable (U : Ultrafilter ℕ) (hfree : (U : Filter ℕ) ≤ atTop)
variable (hsimple : TopologicallySimple A) (hinf : ¬FiniteDimensional ℂ A)
variable (hcmp : StrictComparison A) (hnuc : IsNuclear A)
local notation "τ" => (fun t : TracialState A => t)
local notation "D" => FamilyUltrapower τ U
local notation "Λ" => familyLimitTrace τ U
include hfree hsimple hinf hcmp hnuc in
theorem comparison_set_halving (S : Set D) (hS : S.Countable) :
    ∃ p : D, IsStarProjection p ∧ ∀ a ∈ S, p*a=a*p ∧
      ∀ s : ℕ → TracialState A, (Λ s).functional (p*a)=(1/2:ℂ)*(Λ s).functional a := by
  obtain ⟨x,hx⟩ := Set.countable_iff_exists_subset_range.mp hS
  obtain ⟨p,hp,ht⟩ := comparison_relative_halving U hfree hsimple hinf hcmp hnuc x
  refine ⟨p,hp,?_⟩
  intro a ha
  obtain ⟨k,rfl⟩ := hx ha
  exact ht k
include hfree hsimple hinf hcmp hnuc in
theorem comparison_corner_halving (S : Set D) (hS : S.Countable)
    {r : D} (hr : IsStarProjection r) (hrc : ∀ a ∈ S, Commute r a) :
    ∃ p : D, IsStarProjection p ∧ p ≤ r ∧ ∀ a ∈ S, Commute p a ∧
      ∀ s : ℕ → TracialState A,
        (Λ s).functional (p*a)=(1/2:ℂ)*(Λ s).functional (r*a) := by
  let T := S ∪ (r * ·) '' S ∪ {r}
  have hT : T.Countable := (hS.union (hS.image _)).union (Set.countable_singleton r)
  obtain ⟨p,hp,ht⟩ := comparison_set_halving U hfree hsimple hinf hcmp hnuc T hT
  have hpr : Commute p r := (ht r (Or.inr rfl)).1
  have hrp : IsStarProjection (r*p) := hr.mul hp hpr.symm
  have hrpr : r*p ≤ r := (hrp.le_iff_mul_eq_right hr).mpr (by rw [←mul_assoc,hr.isIdempotentElem.eq])
  refine ⟨r*p,hrp,hrpr,?_⟩
  intro a ha
  have hpa : Commute p a := (ht a (Or.inl (Or.inl ha))).1
  refine ⟨(hrc a ha).mul_left hpa,?_⟩
  intro s
  have h := (ht (r*a) (Or.inl (Or.inr ⟨a,ha,rfl⟩))).2 s
  simpa only [←mul_assoc,hpr.eq] using h

end DirectComparison
end

end OAI
