import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Comparison.DyadicApproximation
import OAI.Analysis.JiangSu.CentralSequences.CoefficientSaturation

namespace OAI

noncomputable section
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
theorem comparison_exact_relative_cut (S : Set D) (hS : S.Countable)
    {r : D} (hr : IsStarProjection r) (hrc : ∀ a ∈ S, Commute r a)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    ∃ p : D, IsStarProjection p ∧ p ≤ r ∧ ∀ a ∈ S, Commute p a ∧
      ∀ s : ℕ → TracialState A, (Λ s).functional (p*a)=(t:ℂ)*(Λ s).functional (r*a) := by
  classical
  let T := S ∪ {0}
  have hT : T.Countable := hS.union (Set.countable_singleton 0)
  obtain ⟨x,hx⟩ := hT.exists_eq_range ⟨0,Or.inr rfl⟩
  have hxT (k : ℕ) : x k ∈ T := hx ▸ Set.mem_range_self k
  have hrT : ∀ a ∈ T, Commute r a := by
    intro a ha
    rcases ha with ha | rfl
    · exact hrc a ha
    · exact Commute.zero_right r
  choose p α hp hpr hα herr hpt using fun n =>
    comparison_dyadic_approximation U hfree hsimple hinf hcmp hnuc T hT n hr hrT ht
  have htr (k : ℕ) : Tendsto (fun n => familyTraceNorm Λ (p n*x k-(t:ℂ) • (r*x k))) atTop (𝓝 0) := by
    have hbound (n : ℕ) : familyTraceNorm Λ (p n*x k-(t:ℂ) • (r*x k)) ≤
        (1/2:ℝ)^n*‖r*x k‖ := by
      apply ciSup_le
      intro s
      rw [map_sub,map_smul,(hpt n (x k) (hxT k)).2 s,smul_eq_mul,←sub_mul,
        ←Complex.ofReal_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs]
      exact mul_le_mul (herr n)
        ((traceNorm_le_family Λ s (r*x k)).trans (familyTraceNorm_le_norm Λ _))
        (norm_nonneg _) (by positivity)
    have hlim : Tendsto (fun n : ℕ => (1/2:ℝ)^n*‖r*x k‖) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_abs_lt_one (r := (1/2:ℝ)) (by norm_num)).mul_const ‖r*x k‖
    exact squeeze_zero (fun n => familyTraceNorm_nonneg Λ _) hbound hlim
  obtain ⟨q,hq,hqr,hqt⟩ := coefficient_projection_saturation τ U hfree x hr (t:ℂ) p hp hpr
    (fun n k => (hpt n (x k) (hxT k)).1.eq) htr
  refine ⟨q,hq,hqr,?_⟩
  intro a ha
  have har : a ∈ Set.range x := hx ▸ Or.inl ha
  obtain ⟨k,rfl⟩ := har
  exact hqt k

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
theorem comparison_relative_partition (S : Set D) (hS : S.Countable)
    (m : ℕ) (hm : 0 < m) {r : D} (hr : IsStarProjection r)
    (hrc : ∀ a ∈ S, Commute r a) :
    ∃ p : Fin m → D, (∀ i, IsStarProjection (p i) ∧ p i ≤ r) ∧
      Pairwise (fun i j => p i*p j=0) ∧ (∑ i, p i)=r ∧
      ∀ i a, a ∈ S → Commute (p i) a ∧ ∀ s : ℕ → TracialState A,
        (Λ s).functional (p i*a)=(1/(m:ℂ))*(Λ s).functional (r*a) := by
  classical
  induction m generalizing r with
  | zero => omega
  | succ n ih =>
    by_cases hn0 : n=0
    · subst n
      refine ⟨fun _ => r,fun i => ⟨hr,le_rfl⟩,?_,?_,?_⟩
      · intro i j hij
        exact (hij (Fin.ext (by omega))).elim
      · simp
      · intro i a ha
        exact ⟨hrc a ha,by intro s; simp⟩
    · have hn : 0 < n := Nat.pos_of_ne_zero hn0
      have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
      have htf : (1/((n:ℝ)+1)) ∈ Set.Icc 0 1 := by
        constructor
        · positivity
        · exact (div_le_one (by positivity)).mpr (by linarith)
      obtain ⟨h,hh,hhr,hht⟩ := comparison_exact_relative_cut U hfree hsimple hinf hcmp hnuc S hS hr hrc htf
      have hhr' : h*r=h := (hh.le_iff_mul_eq_left hr).mp hhr
      have hrem : IsStarProjection (r-h) := hh.sub_of_mul_eq_left hr hhr'
      have hremc : ∀ a ∈ S, Commute (r-h) a := fun a ha =>
        (hrc a ha).sub_left (hht a ha).1
      obtain ⟨p,hp,horth,hsum,hpt⟩ := ih hn hrem hremc
      have hcross (i : Fin n) : h*p i=0 := by
        have hf := ((hp i).1.le_iff_mul_eq_right hrem).mp (hp i).2
        calc
          h*p i=h*((r-h)*p i) := by rw [hf]
          _=(h*(r-h))*p i := (mul_assoc _ _ _).symm
          _=0 := by rw [mul_sub,hhr',hh.isIdempotentElem.eq,sub_self,zero_mul]
      have hcross' (i : Fin n) : p i*h=0 := by
        simpa only [star_mul,hh.isSelfAdjoint.star_eq,(hp i).1.isSelfAdjoint.star_eq,star_zero]
          using congrArg star (hcross i)
      refine ⟨Fin.cons h p,?_,?_,?_,?_⟩
      · intro i
        refine Fin.cases ⟨hh,hhr⟩ (fun j => ?_) i
        exact ⟨(hp j).1,(hp j).2.trans (sub_le_self r hh.nonneg)⟩
      · intro i j
        refine Fin.cases (fun hne => ?_) (fun i' => ?_) i
        · refine Fin.cases (fun hne => (hne rfl).elim) (fun j' _ => ?_) j hne
          simpa using hcross j'
        · refine Fin.cases (fun _ => ?_) (fun j' hij => ?_) j
          · simpa using hcross' i'
          · exact horth (fun he => hij (congrArg Fin.succ he))
      · rw [Fin.sum_univ_succ]
        simp only [Fin.cons_zero,Fin.cons_succ,hsum]
        abel
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · intro a ha
          refine ⟨(hht a ha).1,?_⟩
          intro s
          convert (hht a ha).2 s using 1 <;> push_cast <;> rfl
        · intro a ha
          refine ⟨(hpt j a ha).1,?_⟩
          intro s
          change (Λ s).functional (p j*a)=_
          rw [(hpt j a ha).2 s,sub_mul,map_sub,(hht a ha).2 s]
          have hnC : (n:ℂ) ≠ 0 := by exact_mod_cast hn0
          have hnC' : (n:ℂ)+1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
          push_cast
          field_simp
          ring

end DirectComparison

namespace DirectComparison
open Pureness CurrentMain Filter
open scoped Topology ComplexOrder

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
local notation "τ" => (fun t : TracialState A => t)

variable [Nontrivial A] [Nonempty (TracialState A)] [TopologicalSpace.SeparableSpace A]
variable (U : Ultrafilter ℕ) (hfree : (U : Filter ℕ) ≤ atTop)
variable (hsimple : TopologicallySimple A) (hinf : ¬FiniteDimensional ℂ A)
variable (hcmp : StrictComparison A) (hnuc : IsNuclear A)
local notation "D" => FamilyUltrapower τ U
local notation "Λ" => familyLimitTrace τ U

include hfree hsimple hinf hcmp hnuc in

theorem comparison_uniform_gamma_partition (m : ℕ) (hm : 0 < m) :
    ∃ p : Fin m → D, (∀ i, IsStarProjection (p i)) ∧
      Pairwise (fun i j => p i*p j=0) ∧ (∑ i, p i)=1 ∧
      ∀ i (a : A), Commute (p i) (familyUltrapowerMap τ U a) ∧
      ∀ s : ℕ → TracialState A, (Λ s).functional (familyUltrapowerMap τ U a*p i)=
        (1/(m:ℂ))*(Λ s).functional (familyUltrapowerMap τ U a) := by
  classical
  obtain ⟨x,hx⟩ := TopologicalSpace.exists_dense_seq A
  let ι := familyUltrapowerMap τ U
  have hι : Continuous ι := (ι.toLinearMap.mkContinuous 1 (fun a => by
    change ‖ι a‖ ≤ 1*‖a‖
    simpa only [one_mul] using NonUnitalStarAlgHom.norm_apply_le ι a)).continuous
  let S := Set.range (fun n => ι (x n))
  obtain ⟨p,hp,horth,hsum,hpt⟩ := comparison_relative_partition U hfree hsimple hinf hcmp hnuc
    S (Set.countable_range _) m hm (IsStarProjection.one _) (fun a _ => Commute.one_left a)
  refine ⟨p,fun i => (hp i).1,horth,hsum,?_⟩
  intro i a
  have hcomm : (fun b : A => p i*ι b)=(fun b : A => ι b*p i) :=
    hx.equalizer (continuous_const.mul hι) (hι.mul continuous_const)
      (funext fun n => (hpt i (ι (x n)) (Set.mem_range_self n)).1.eq)
  refine ⟨congrFun hcomm a,?_⟩
  intro s
  have hσ : Continuous (Λ s).functional := map_continuous (Λ s).functional
  have he : (fun b : A => (Λ s).functional (p i*ι b))=
      (fun b : A => (1/(m:ℂ))*(Λ s).functional (ι b)) :=
    hx.equalizer (hσ.comp (continuous_const.mul hι)) (continuous_const.mul (hσ.comp hι))
      (funext fun n => by
        change (Λ s).functional (p i*ι (x n))=(1/(m:ℂ))*(Λ s).functional (ι (x n))
        simpa only [one_mul] using (hpt i (ι (x n)) (Set.mem_range_self n)).2 s)
  rw [←(Λ s).tracial]
  exact congrFun he a

include hfree hsimple hinf hcmp hnuc in

theorem comparison_uniform_gamma : UniformGamma A U := by
  intro m hm
  obtain ⟨p,hp,_,hsum,hpt⟩ := comparison_uniform_gamma_partition U hfree hsimple hinf hcmp hnuc m hm
  exact ⟨p,hp,hsum,fun i a => (hpt i a).1,fun i a s => (hpt i a).2 s⟩

end DirectComparison
end

end OAI
