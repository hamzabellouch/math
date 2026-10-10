import Mathlib
import OAI.MathematicalPhysics.BFSS.StabilizerProfiles

namespace OAI

/-! Joint energy, closed-profile norm exhaustion and finite-family limits. -/

namespace BFSSQuantum
noncomputable section
open MeasureTheory Set Filter

def jointEnergy {N : ℕ} (y : SpinIndex → FullL2 N) : ℝ :=
  (1/16 : ℝ) * ∑ α : SpinIndex, ‖y α‖^2

lemma jointEnergy_continuous {N : ℕ} : Continuous (@jointEnergy N) := by
  apply Continuous.const_mul
  exact continuous_finsetSum _ (fun α _ => (continuous_apply α).norm.pow 2)

lemma jointEnergy_nonneg {N : ℕ} (y : SpinIndex → FullL2 N) : 0 ≤ jointEnergy y :=
  mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => sq_nonneg _)

namespace AlgebraData
variable {N : ℕ} (M : AlgebraData N)
lemma jointEnergy_core (h m : ℝ) (f : SmoothCore N) :
    jointEnergy (M.deformedChargeVector h m f) = M.deformedCoreEnergy h m f := rfl

namespace GaugeData
variable {M} (G : M.GaugeData)
attribute [local irreducible] AlgebraData.normalSlice AlgebraData.gaugeAction coreToL2
  MeasuredNormalPatch.closedProfile

lemma deformedModelGraph_closure_subtype (h m : ℝ)
    {x : G.coreNormClosure} {y : SpinIndex → FullL2 N}
    (hp : ((x : FullL2 N),y) ∈ G.deformedModelGraph h m) :
    (x,y) ∈ closure (range (fun f : G.invariantCore =>
      (G.coreNormEmbedding f,M.deformedChargeVector h m f.val))) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨p,⟨f,rfl⟩,hd⟩ := Metric.mem_closure_iff.mp hp ε hε
  exact ⟨(G.coreNormEmbedding f,M.deformedChargeVector h m f.val),mem_range_self f,hd⟩

attribute [local irreducible] MeasuredNormalPatch.profile coreNormEmbedding
  AlgebraData.deformedCoreEnergy jointEnergy AlgebraData.deformedChargeVector

lemma normalPatch_closedSet {S : Finset (Boson N)} (P : (q : S) → G.MeasuredNormalPatch q.val)
    (h A K : ℝ) : IsClosed {p : G.coreNormClosure × (SpinIndex → FullL2 N) |
      0 ≤ ‖p.1‖^2 - ∑ q : S, ‖(P q).closedProfile h p.1‖^2 ∧
      A*(‖p.1‖^2 - ∑ q : S, ‖(P q).closedProfile h p.1‖^2) ≤
        h^2*(jointEnergy p.2 + K*‖p.1‖^2)} := by
  let D := G.coreNormClosure × (SpinIndex → FullL2 N)
  have hnorm : Continuous (fun p : D => ‖p.1‖^2) := continuous_fst.norm.pow 2
  have hloss : Continuous (fun p : D => ‖p.1‖^2 - ∑ q : S, ‖(P q).closedProfile h p.1‖^2) :=
    hnorm.sub (continuous_finsetSum _ (fun q _ =>
      (((P q).closedProfile h).continuous.comp continuous_fst).norm.pow 2))
  exact (isClosed_le continuous_const hloss).inter
    (isClosed_le (hloss.const_mul A)
      (((jointEnergy_continuous.comp continuous_snd).add (hnorm.const_mul K)).const_mul (h^2)))

lemma normalPatch_bound_closed {S : Finset (Boson N)} (P : (q : S) → G.MeasuredNormalPatch q.val)
    (h : ℝ) (hh : 0 < h) (h1 : h ≤ 1) (A K : ℝ)
    (hb : ∀ f : G.invariantCore,
      0 ≤ ‖coreToL2 f.val‖^2 - ∑ q : S, ‖(P q).profile h f‖^2 ∧
      A*(‖coreToL2 f.val‖^2 - ∑ q : S, ‖(P q).profile h f‖^2) ≤
        h^2*(M.deformedCoreEnergy h 1 f.val + K*‖coreToL2 f.val‖^2))
    {x : G.coreNormClosure} {y : SpinIndex → FullL2 N}
    (hg : ((x : FullL2 N),y) ∈ G.deformedModelGraph h 1) :
    0 ≤ ‖x‖^2 - ∑ q : S, ‖(P q).closedProfile h x‖^2 ∧
      A*(‖x‖^2 - ∑ q : S, ‖(P q).closedProfile h x‖^2) ≤
        h^2*(jointEnergy y + K*‖x‖^2) := by
  have hc := G.normalPatch_closedSet P h A K
  apply closure_minimal (s := range (fun f : G.invariantCore =>
    (G.coreNormEmbedding f,M.deformedChargeVector h 1 f.val))) _ hc
      (G.deformedModelGraph_closure_subtype h 1 hg)
  rintro _ ⟨f,rfl⟩
  change 0 ≤ ‖G.coreNormEmbedding f‖^2 - ∑ q : S, ‖(P q).closedProfile h (G.coreNormEmbedding f)‖^2 ∧
    A*(‖G.coreNormEmbedding f‖^2 - ∑ q : S, ‖(P q).closedProfile h (G.coreNormEmbedding f)‖^2) ≤
      h^2*(jointEnergy (M.deformedChargeVector h 1 f.val)+K*‖G.coreNormEmbedding f‖^2)
  have hp (q : S) : (P q).closedProfile h (G.coreNormEmbedding f) = (P q).profile h f :=
    (P q).closedProfile_core hh h1 f
  simp only [hp,G.coreNormEmbedding_norm,M.jointEnergy_core]
  exact hb f

theorem normalClosed_norm_exhaustion (hN : 2 ≤ N) :
    ∃ S : Finset (Boson N),
      (∀ q ∈ S, q ∈ M.massiveZeros) ∧
      M.massiveZeros = ⋃ q ∈ S, M.gaugeOrbit q ∧
      Pairwise (fun i j : S => Disjoint (M.gaugeOrbit i.val) (M.gaugeOrbit j.val)) ∧
      ∃ P : (q : S) → G.MeasuredNormalPatch q.val,
        ∃ A K : ℝ, 0 < A ∧ 0 ≤ K ∧
          ∀ (h : ℝ), 0 < h → h ≤ 1 →
            ∀ (x : G.coreNormClosure) (y : SpinIndex → FullL2 N),
              ((x : FullL2 N),y) ∈ G.deformedModelGraph h 1 →
              0 ≤ ‖x‖^2 - ∑ q : S, ‖(P q).closedProfile h x‖^2 ∧
              A*(‖x‖^2 - ∑ q : S, ‖(P q).closedProfile h x‖^2) ≤
                h^2*(jointEnergy y + K*‖x‖^2) := by
  classical
  have hexhaustion := G.normalPatch_norm_exhaustion hN
  let S := hexhaustion.choose
  have hfamily := hexhaustion.choose_spec
  refine ⟨S,hfamily.1,hfamily.2.1,hfamily.2.2.1,?_⟩
  let P := hfamily.2.2.2.choose
  have hpatch := hfamily.2.2.2.choose_spec
  let δ := hpatch.2.choose
  have hdelta := hpatch.2.choose_spec
  let c := hdelta.choose
  have hcoefficient := hdelta.choose_spec
  let K := hcoefficient.choose
  have hconstants := hcoefficient.choose_spec
  refine ⟨P,c/2*δ^2,K,
    mul_pos (half_pos hconstants.2.1) (sq_pos_of_pos hconstants.1),hconstants.2.2.1,?_⟩
  intro h hh h1 x y hg
  apply G.normalPatch_bound_closed P h hh h1 (c/2*δ^2) K _ hg
  intro f
  have hb := hconstants.2.2.2 h hh h1 f
  simpa only [MeasuredNormalPatch.profile_norm_square] using hb
end GaugeData
end AlgebraData
end
end BFSSQuantum
namespace BFSSRellich
noncomputable section
open Set Filter
open scoped Pointwise
lemma totallyBounded_asymptotic {X : Type*} [NormedAddCommGroup X] [CompleteSpace X]
    (a b : ℕ → X) (ha : TotallyBounded (range a))
    (hd : Tendsto (fun n => dist (a n) (b n)) atTop (nhds 0)) :
    TotallyBounded (range b) := by
  have ht : Tendsto (fun n => b n-a n) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [←dist_eq_norm,dist_comm] using hd
  have hc := (ha.closure.isCompact_of_isClosed isClosed_closure).add ht.isCompact_insert_range
  apply hc.totallyBounded.subset
  rintro _ ⟨n,rfl⟩
  exact ⟨a n, subset_closure (mem_range_self n), b n-a n,
    Or.inr (mem_range_self n), add_sub_cancel _ _⟩
end
end BFSSRellich

namespace BFSSQuantum.AlgebraData.GaugeData.MeasuredNormalPatch
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal
variable {N : ℕ} {M : AlgebraData N} {G : M.GaugeData}
variable {q : Boson N} (P : G.MeasuredNormalPatch q)
attribute [local irreducible] AlgebraData.normalSlice AlgebraData.gaugeAction coreToL2 closedProfile

lemma closedProfile_totallyBounded (hN : 2 ≤ N)
    (h : ℕ → ℝ) (hh : ∀ n, 0 < h n ∧ h n ≤ 1) (hzero : Tendsto h atTop (nhds 0))
    (x : ℕ → G.coreNormClosure) (y : ℕ → SpinIndex → FullL2 N) (B : ℝ≥0)
    (hg : ∀ n, ((x n : FullL2 N),y n) ∈ G.deformedModelGraph (h n) 1)
    (hx : ∀ n, ‖x n‖ ≤ B) (hy : ∀ n α, ‖y n α‖ ≤ B) :
    TotallyBounded (range (fun n => P.closedProfile (h n) (x n))) := by
  classical
  let ε : ℕ → ℝ := fun n => 1/((n : ℝ)+1)
  have hε (n : ℕ) : 0 < ε n := one_div_pos.mpr (by positivity)
  have hε1 (n : ℕ) : ε n ≤ 1 := by
    apply (div_le_iff₀ (show 0 < (n : ℝ)+1 by positivity)).2
    simp only [one_mul]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hεzero : Tendsto ε atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  choose f hf hQ using (fun n => G.deformedModelGraph_approx (h n) 1 (hg n) (ε n) (hε n))
  let C : ℝ≥0 := B+1
  have hcf (n : ℕ) : ‖coreToL2 (f n).val‖ ≤ C := by
    have hd : dist (coreToL2 (f n).val) (x n : FullL2 N) ≤ 1 :=
      by rw [dist_comm]; exact (hf n).le.trans (hε1 n)
    have ha := norm_le_norm_add_const_of_dist_le hd
    change _ ≤ (B : ℝ)+1
    exact ha.trans (add_le_add (show ‖(x n : FullL2 N)‖ ≤ B from hx n) le_rfl)
  have hqf (n : ℕ) (α : SpinIndex) : ‖coreToL2 (M.deformedCoreCharge (h n) 1 α (f n).val)‖ ≤ C := by
    have hd : dist (coreToL2 (M.deformedCoreCharge (h n) 1 α (f n).val)) (y n α) ≤ 1 :=
      by rw [dist_comm]; exact (hQ n α).le.trans (hε1 n)
    have ha := norm_le_norm_add_const_of_dist_le hd
    change _ ≤ (B : ℝ)+1
    linarith [hy n α]
  have hfs (n : ℕ) : ‖coreToL2 (f n).val‖^2 ≤ (C^2 : ℝ≥0) :=
    pow_le_pow_left₀ (norm_nonneg _) (hcf n) 2
  have he (n : ℕ) : M.deformedCoreEnergy (h n) 1 (f n).val ≤ (C^2 : ℝ≥0) := by
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun α _ =>
      pow_le_pow_left₀ (norm_nonneg _) (hqf n α) 2)
    unfold AlgebraData.deformedCoreEnergy
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
    norm_num only [Nat.cast_ofNat] at hs
    change _ ≤ (C : ℝ)^2
    linarith
  have hdist : Tendsto (fun n => dist (P.profile (h n) (f n))
      (P.closedProfile (h n) (x n))) atTop (nhds 0) := by
    apply squeeze_zero (fun _ => dist_nonneg) _ hεzero
    intro n
    exact (P.closedProfile_core_dist_le (hh n).1 (hh n).2 (f n) (x n)).trans
      (by rw [dist_comm]; exact (hf n).le)
  exact BFSSRellich.totallyBounded_asymptotic _ _
    (P.profile_totallyBounded hN h hh hzero f (C^2) hfs he) hdist
end
end BFSSQuantum.AlgebraData.GaugeData.MeasuredNormalPatch
namespace BFSSQuantum
noncomputable section
open MeasureTheory Set Filter
lemma jointEnergy_le {N : ℕ} (y : SpinIndex → FullL2 N) {B : ℝ}
    (_hB : 0 ≤ B) (hy : ∀ α, ‖y α‖ ≤ B) : jointEnergy y ≤ B^2 := by
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun α _ =>
    pow_le_pow_left₀ (norm_nonneg _) (hy α) 2)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
  norm_num only [Nat.cast_ofNat] at hs
  unfold jointEnergy
  linarith

namespace AlgebraData.GaugeData
variable {N : ℕ} {M : AlgebraData N} (G : M.GaugeData)
attribute [local irreducible] AlgebraData.normalSlice AlgebraData.gaugeAction coreToL2
  MeasuredNormalPatch.closedProfile

lemma normalFamily_normlimit {S : Finset (Boson N)} (P : (q : S) → G.MeasuredNormalPatch q.val)
    (A K E : ℝ) (hA : 0 < A) (hK : 0 ≤ K)
    (h : ℕ → ℝ) (hzero : Tendsto h atTop (nhds 0))
    (x : ℕ → G.coreNormClosure) (y : ℕ → SpinIndex → FullL2 N)
    (hx : ∀ n, ‖x n‖^2 ≤ E) (hy : ∀ n, jointEnergy (y n) ≤ E)
    (hb : ∀ n, 0 ≤ ‖x n‖^2 - ∑ q : S, ‖(P q).closedProfile (h n) (x n)‖^2 ∧
      A*(‖x n‖^2 - ∑ q : S, ‖(P q).closedProfile (h n) (x n)‖^2) ≤
        (h n)^2*(jointEnergy (y n) + K*‖x n‖^2))
    (v : (q : S) → Lp (Fermion N) 2 (volume : Measure (M.NormalCoordinates q.val)))
    (hv : ∀ q, Tendsto (fun n => (P q).closedProfile (h n) (x n)) atTop (nhds (v q))) :
    Tendsto (fun n => ‖x n‖^2) atTop (nhds (∑ q : S, ‖v q‖^2)) := by
  let r : ℕ → ℝ := fun n => ‖x n‖^2 - ∑ q : S, ‖(P q).closedProfile (h n) (x n)‖^2
  have hr (n : ℕ) : 0 ≤ r n ∧ r n ≤ (h n)^2*((E+K*E)/A) := by
    refine ⟨(hb n).1,?_⟩
    rw [←mul_div_assoc]
    apply (le_div_iff₀ hA).2
    have he : jointEnergy (y n) + K*‖x n‖^2 ≤ E+K*E :=
      add_le_add (hy n) (mul_le_mul_of_nonneg_left (hx n) hK)
    have hs := (hb n).2.trans (mul_le_mul_of_nonneg_left he (sq_nonneg _))
    change r n * A ≤ _
    rw [mul_comm (r n)]
    exact hs
  have hrzero : Tendsto r atTop (nhds 0) :=
    squeeze_zero (fun n => (hr n).1) (fun n => (hr n).2)
      (by simpa using (hzero.pow 2).mul_const ((E+K*E)/A))
  have hsum : Tendsto (fun n => ∑ q : S, ‖(P q).closedProfile (h n) (x n)‖^2) atTop
      (nhds (∑ q : S, ‖v q‖^2)) := tendsto_finsetSum _ (fun q _ => (hv q).norm.pow 2)
  simpa only [r,zero_add,sub_add_cancel] using hrzero.add hsum
end AlgebraData.GaugeData
end
end BFSSQuantum
namespace BFSSQuantum.AlgebraData.GaugeData
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal
variable {N : ℕ} {M : AlgebraData N} (G : M.GaugeData)
attribute [local irreducible] AlgebraData.normalSlice AlgebraData.gaugeAction coreToL2
  MeasuredNormalPatch.closedProfile coreNormClosure invariantCore deformedModelGraph
  normalEquivariantSpace

lemma graph_linearCombination {ι : Type*} [Fintype ι] (h m : ℝ)
    (a : ι → ℂ) (x : ι → G.coreNormClosure) (y : ι → SpinIndex → FullL2 N)
    (hg : ∀ i, ((x i : FullL2 N),y i) ∈ G.deformedModelGraph h m) :
    (((∑ i, a i • x i : G.coreNormClosure) : FullL2 N),∑ i, a i • y i) ∈
      G.deformedModelGraph h m := by
  have hs := (G.deformedModelGraph h m).sum_mem (t := Finset.univ)
    (fun i _ => (G.deformedModelGraph h m).smul_mem (a i) (hg i))
  convert hs using 1
  apply Prod.ext <;> simp only [Submodule.coe_sum,Submodule.coe_smul,
    Prod.fst_sum,Prod.snd_sum,Prod.smul_fst,Prod.smul_snd]

lemma linearCombination_norm_le {ι X : Type*} [Fintype ι] [NormedAddCommGroup X]
    [NormedSpace ℂ X] (a : ι → ℂ) (x : ι → X) (B : ℝ) (hx : ∀ i, ‖x i‖ ≤ B) :
    ‖∑ i, a i • x i‖ ≤ (∑ i, ‖a i‖)*B := by
  calc
    ‖∑ i, a i • x i‖ ≤ ∑ i, ‖a i • x i‖ := norm_sum_le _ _
    _ = ∑ i, ‖a i‖*‖x i‖ := by simp only [norm_smul]
    _ ≤ ∑ i, ‖a i‖*B := Finset.sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_left (hx i) (norm_nonneg _))
    _ = (∑ i, ‖a i‖)*B := (Finset.sum_mul _ _ _).symm

def NormalFamilyConclusion {ι : Type*} [Fintype ι]
    (h : ℕ → ℝ) (x : ℕ → ι → G.coreNormClosure) : Prop :=
    ∃ S : Finset (Boson N),
      (∀ q ∈ S, q ∈ M.massiveZeros) ∧
      M.massiveZeros = ⋃ q ∈ S, M.gaugeOrbit q ∧
      Pairwise (fun i j : S => Disjoint (M.gaugeOrbit i.val) (M.gaugeOrbit j.val)) ∧
      ∃ P : (q : S) → G.MeasuredNormalPatch q.val,
        ∃ v : ι → (q : S) → Lp (Fermion N) 2 (volume : Measure (M.NormalCoordinates q.val)),
          ∃ σ : ℕ → ℕ, StrictMono σ ∧
            (∀ i q, v i q ∈ G.normalEquivariantSpace q.val) ∧
            (∀ i q, Tendsto (fun n => (P q).closedProfile (h (σ n)) (x (σ n) i))
              atTop (nhds (v i q))) ∧
            (∀ a : ι → ℂ, Tendsto (fun n => ‖∑ i, a i • x (σ n) i‖^2) atTop
              (nhds (∑ q : S, ‖∑ i, a i • v i q‖^2)))

theorem normalClosed_finiteFamily (hN : 2 ≤ N) {ι : Type*} [Fintype ι]
    (h : ℕ → ℝ) (hh : ∀ n, 0 < h n ∧ h n ≤ 1) (hzero : Tendsto h atTop (nhds 0))
    (x : ℕ → ι → G.coreNormClosure) (y : ℕ → ι → SpinIndex → FullL2 N) (B : ℝ≥0)
    (hg : ∀ n i, ((x n i : FullL2 N),y n i) ∈ G.deformedModelGraph (h n) 1)
    (hx : ∀ n i, ‖x n i‖ ≤ B) (hy : ∀ n i α, ‖y n i α‖ ≤ B) :
    G.NormalFamilyConclusion h x := by
  classical
  unfold NormalFamilyConclusion
  obtain ⟨S,hS,hcov,hdis,P,A,K,hA,hK,hbound⟩ := G.normalClosed_norm_exhaustion hN
  let X (q : S) := Lp (Fermion N) 2 (volume : Measure (M.NormalCoordinates q.val))
  let f : ℕ → (ι → (q : S) → X q) := fun n i q => (P q).closedProfile (h n) (x n i)
  have hcompact (i : ι) (q : S) : IsCompact (closure (range (fun n => f n i q))) :=
    ((P q).closedProfile_totallyBounded hN h hh hzero (fun n => x n i) (fun n => y n i) B
      (fun n => hg n i) (fun n => hx n i) (fun n α => hy n i α)).closure.isCompact_of_isClosed
        isClosed_closure
  have hp := isCompact_pi_infinite (fun i => isCompact_pi_infinite (hcompact i))
  obtain ⟨v,_,σ,hσ,ht⟩ := hp.tendsto_subseq (fun n i q => subset_closure (mem_range_self n))
  have hcoord (i : ι) (q : S) : Tendsto (fun n => (P q).closedProfile (h (σ n)) (x (σ n) i))
      atTop (nhds (v i q)) := (tendsto_pi_nhds.mp ((tendsto_pi_nhds.mp ht) i)) q
  refine ⟨S,hS,hcov,hdis,P,v,σ,hσ,?_,hcoord,?_⟩
  · intro i q
    exact (P q).limit_mem_equivariantSpace (fun n => h (σ n)) (fun n => hh (σ n))
      (fun n => x (σ n) i) (hcoord i q)
  · intro a
    let C : ℝ := (∑ i, ‖a i‖)*(B : ℝ)
    have hC : 0 ≤ C := mul_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _) B.prop
    have hxc (n : ℕ) : ‖∑ i, a i • x (σ n) i‖ ≤ C :=
      linearCombination_norm_le a _ _ (fun i => hx (σ n) i)
    have hyc (n : ℕ) (α : SpinIndex) : ‖(∑ i, a i • y (σ n) i) α‖ ≤ C := by
      simpa only [Finset.sum_apply,Pi.smul_apply] using
        linearCombination_norm_le a (fun i => y (σ n) i α) (B : ℝ) (fun i => hy (σ n) i α)
    apply G.normalFamily_normlimit P A K (C^2) hA hK (fun n => h (σ n))
      (hzero.comp hσ.tendsto_atTop) (fun n => ∑ i, a i • x (σ n) i)
      (fun n => ∑ i, a i • y (σ n) i)
      (fun n => pow_le_pow_left₀ (norm_nonneg _) (hxc n) 2)
      (fun n => jointEnergy_le _ hC (hyc n))
    · intro n
      exact hbound _ (hh (σ n)).1 (hh (σ n)).2 _ _
        (G.graph_linearCombination _ _ a _ _ (hg (σ n)))
    · intro q
      have hz := tendsto_finsetSum (s := Finset.univ) (fun i _ => (hcoord i q).const_smul (a i))
      simpa only [map_sum,map_smul] using hz
end
end BFSSQuantum.AlgebraData.GaugeData

end OAI
