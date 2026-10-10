import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Comparison.ProjectionDefect
import OAI.Analysis.JiangSu.Nonunital.TracialState

namespace OAI

noncomputable section
namespace NonunitalGamma
open Filter Topology
open scoped ComplexOrder

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma NormalizedTrace.toWeakDual_injective :
    Function.Injective (NormalizedTrace.toWeakDual (A := A)) := by
  intro τ σ h
  have hf : τ.functional=σ.functional := PositiveLinearMap.ext
    (fun a => congrArg (fun f : WeakDual ℂ A => f a) h)
  cases τ
  cases σ
  congr

lemma NormalizedTrace.continuous_eval (a : A) :
    Continuous (fun τ : NormalizedTrace A => τ.functional a) := by
  change Continuous ((fun f : WeakDual ℂ A => f a) ∘ NormalizedTrace.toWeakDual)
  exact (WeakDual.eval_continuous a).comp continuous_induced_dom

lemma NormalizedTrace.continuous_eval_re (a : A) :
    Continuous (fun τ : NormalizedTrace A => (τ.functional a).re) :=
  Complex.continuous_re.comp (NormalizedTrace.continuous_eval a)

abbrev StrictPositiveContraction (A : Type*) [NonUnitalCStarAlgebra A] [PartialOrder A] :=
  {b : A // 0 ≤ b ∧ ‖b‖ < 1}

lemma strictPositiveContraction_directed (a b : StrictPositiveContraction A) :
    ∃ c : StrictPositiveContraction A, a.1 ≤ c.1 ∧ b.1 ≤ c.1 := by
  obtain ⟨c,hc,hac,hbc⟩ := CStarAlgebra.directedOn_nonneg_ball a.1
    (by simpa only [Set.mem_inter_iff,Set.mem_ofPred_eq,Metric.mem_ball,dist_zero_right] using a.2)
    b.1 (by simpa only [Set.mem_inter_iff,Set.mem_ofPred_eq,Metric.mem_ball,dist_zero_right] using b.2)
  exact ⟨⟨c,by simpa only [Set.mem_inter_iff,Set.mem_ofPred_eq,Metric.mem_ball,dist_zero_right] using hc⟩,hac,hbc⟩

theorem uniform_trace_approximate_unit [CompactSpace (NormalizedTrace A)]
    (ε : ℝ) (hε : 0 < ε) :
    ∃ b : A, 0 ≤ b ∧ ‖b‖ < 1 ∧ ∀ τ : NormalizedTrace A,
      1-ε < (τ.functional b).re := by
  let V (b : StrictPositiveContraction A) :=
    {τ : NormalizedTrace A | 1-ε < (τ.functional b.1).re}
  have hopen (b : StrictPositiveContraction A) : IsOpen (V b) :=
    isOpen_lt continuous_const (NormalizedTrace.continuous_eval_re b.1)
  have hcover (τ : NormalizedTrace A) (_hτ : τ ∈ (Set.univ : Set (NormalizedTrace A))) :
      τ ∈ ⋃ b : StrictPositiveContraction A, V b := by
    have hbound : max (1-ε) 0 < 1 := max_lt (sub_lt_self _ hε) zero_lt_one
    obtain ⟨c,hc,hc1⟩ := exists_between hbound
    obtain ⟨b,hb,hbn,hbt⟩ := τ.exists_positive_trace_gt
      ((le_max_right (1-ε) 0).trans_lt hc) hc1
    apply Set.mem_iUnion.mpr
    exact ⟨⟨b,hb,hbn⟩,((le_max_left (1-ε) 0).trans_lt hc).trans hbt⟩
  have hdir : Directed (· ⊆ ·) V := by
    intro a b
    obtain ⟨c,hac,hbc⟩ := strictPositiveContraction_directed a b
    refine ⟨c,?_,?_⟩
    · intro τ hτ
      exact hτ.trans_le (τ.functional.monotone hac).1
    · intro τ hτ
      exact hτ.trans_le (τ.functional.monotone hbc).1
  let : Nonempty (StrictPositiveContraction A) := ⟨⟨0,le_rfl,by simp⟩⟩
  obtain ⟨b,hb⟩ := isCompact_univ.elim_directed_cover V hopen hcover hdir
  exact ⟨b.1,b.2.1,b.2.2,fun τ => hb (Set.mem_univ τ)⟩

end NonunitalGamma

namespace NonunitalGamma
open Pureness CurrentMain Filter Topology
open scoped ComplexOrder ENNReal

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

@[simp] lemma NormalizedTrace.unitized_inr (τ : NormalizedTrace A) (a : A) :
    τ.unitized.functional (Unitization.inr a)=τ.functional a := unitizedFunctional_inr τ.functional τ.norm_one.le a

local notation "T" => (fun τ : NormalizedTrace A => NormalizedTrace.unitized τ)

omit [PartialOrder A] [StarOrderedRing A] in
lemma nonunital_lp_unitized_nonneg (e : lp (fun _ : ℕ => Unitization ℂ A) ∞)
    (he : ∀ n, 0 ≤ e n) : 0 ≤ e := by
  let Q : lp (fun _ : ℕ => Unitization ℂ A) ∞ :=
    ⟨fun n => CFC.sqrt (e n),memℓp_infty_iff.mpr ⟨Real.sqrt ‖e‖,by
      rintro _ ⟨n,rfl⟩
      exact (CFC.norm_sqrt (e n) (he n)).le.trans
        (Real.sqrt_le_sqrt (lp.norm_apply_le_norm ENNReal.top_ne_zero e n))⟩⟩
  have h : e=star Q*Q := by
    apply Subtype.ext
    funext n
    change e n=star (CFC.sqrt (e n))*CFC.sqrt (e n)
    rw [(CFC.sqrt_nonneg _).isSelfAdjoint.star_eq,CFC.sqrt_mul_sqrt_self _ (he n)]
  rw [h]
  exact star_mul_self_nonneg Q

theorem exists_unit_representative [Nonempty (NormalizedTrace A)]
    [CompactSpace (NormalizedTrace A)] (U : Ultrafilter ℕ)
    (hfree : (U : Filter ℕ) ≤ atTop) :
    ∃ e : lp (fun _ : ℕ => Unitization ℂ A) ∞,
      (∀ n, (e n).fst=0) ∧ 0 ≤ e ∧ ‖e‖ ≤ 1 ∧
      (familyNullIdeal T (U : Filter ℕ)).quotientMap e=1 := by
  let δ : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have hδ (n : ℕ) : 0 < δ n := by dsimp [δ]; positivity
  choose b hb hbn hbt using fun n => uniform_trace_approximate_unit (A := A) (δ n) (hδ n)
  let e : lp (fun _ : ℕ => Unitization ℂ A) ∞ :=
    ⟨fun n => Unitization.inr (b n),memℓp_infty_iff.mpr ⟨1,by
      rintro _ ⟨n,rfl⟩
      simpa only [Unitization.norm_inr] using (hbn n).le⟩⟩
  have he0 : 0 ≤ e := by
    apply nonunital_lp_unitized_nonneg
    intro n
    exact map_nonneg (Unitization.inrNonUnitalStarAlgHom ℂ A) (hb n)
  have hen : ‖e‖ ≤ 1 := lp.norm_le_of_forall_le zero_le_one (fun n => by
    change ‖(b n : Unitization ℂ A)‖ ≤ 1
    simpa only [Unitization.norm_inr] using (hbn n).le)
  let J := familyNullIdeal T (U : Filter ℕ)
  let q := J.quotientMap e
  have hq0 : 0 ≤ q := map_nonneg J.quotientStarHom he0
  have hqn : ‖q‖ ≤ 1 := (J.quotientMap_norm_le e).trans hen
  have hq1 : q ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg q hq0).mp hqn
  have ht (s : ℕ → NormalizedTrace A) : (familyLimitTrace T U s).functional q=1 := by
    have hm := familyLimitTrace_tendsto T U s e
    change Tendsto (fun n => (s n).unitized.functional (Unitization.inr (b n)))
      (U : Filter ℕ) (𝓝 ((familyLimitTrace T U s).functional q)) at hm
    have hlim0 : Tendsto (fun n => 1-((s n).functional (b n)).re) (U : Filter ℕ) (𝓝 0) := by
      apply squeeze_zero (g := δ)
      · intro n
        have hn := (positiveFunctionalCLM (s n).functional).le_opNorm (b n)
        rw [(s n).norm_one,one_mul] at hn
        exact sub_nonneg.mpr ((Complex.re_le_norm _).trans (hn.trans (hbn n).le))
      · intro n
        exact (sub_lt_comm.mp (hbt n (s n))).le
      · exact tendsto_one_div_add_atTop_nhds_zero_nat.mono_left hfree
    have hlim : Tendsto (fun n => ((s n).functional (b n)).re) (U : Filter ℕ) (𝓝 1) := by
      have h := (tendsto_const_nhds (x := (1:ℝ))).sub hlim0
      simpa only [sub_sub_cancel,sub_zero] using h
    have hv : Tendsto (fun n => ((s n).functional (b n)).re) (U : Filter ℕ)
        (𝓝 ((familyLimitTrace T U s).functional q).re) := by
      simpa only [Function.comp_def,NormalizedTrace.unitized_inr] using Complex.continuous_re.continuousAt.tendsto.comp hm
    apply Complex.ext
    · exact tendsto_nhds_unique hv hlim
    · exact ((Complex.nonneg_iff.mp ((familyLimitTrace T U s).functional.map_nonneg hq0)).2).symm
  have hz : 1-q=0 := by
    apply limitTrace_detects_positive_zero T U (1-q) (sub_nonneg.mpr hq1)
    intro s
    simp only [map_sub,(familyLimitTrace T U s).normalized,ht s,sub_self,Complex.zero_re]
  exact ⟨e,fun _ => rfl,he0,hen,(sub_eq_zero.mp hz).symm⟩

end NonunitalGamma

namespace NonunitalGamma
open TraceCone
open scoped ENNReal NNReal ComplexOrder ComplexStarModule

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma weightBounded_denselyFinite {τ : ExtendedTrace A} (hτ : WeightBounded τ) :
    WeightDenselyFinite τ := by
  have he : {a : Positive A | τ a < ∞}=Set.univ := by
    ext a
    simp only [Set.mem_ofPred_eq,Set.mem_univ,iff_true]
    exact lt_top_iff_ne_top.mpr (weightBounded_finite hτ a)
  unfold WeightDenselyFinite
  rw [he]
  exact dense_univ

end NonunitalGamma

end

end OAI
