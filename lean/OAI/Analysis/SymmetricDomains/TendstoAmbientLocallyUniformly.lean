import Mathlib
import OAI.Analysis.SymmetricDomains.HolomorphicLocallyUniformLimit
import OAI.Analysis.SymmetricDomains.FiniteUnion

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology TopologicalSpace
open scoped Classical
namespace Biholomorph

@[ext] theorem ext {n m : ℕ} {U : Set (Affine n)} {V : Set (Affine m)}
    {a b : Biholomorph U V} (h : ∀ x, a.toHomeomorph x=b.toHomeomorph x) : a=b := by
  have he := Homeomorph.ext h
  cases a
  cases b
  cases he
  rfl

noncomputable instance automorphismMul {n : ℕ} {U : Set (Affine n)} : Mul (Biholomorph U U) :=
  ⟨fun a b => b.trans a⟩
noncomputable instance automorphismOne {n : ℕ} {U : Set (Affine n)} : One (Biholomorph U U) :=
  ⟨refl U⟩
noncomputable instance automorphismInv {n : ℕ} {U : Set (Affine n)} : Inv (Biholomorph U U) :=
  ⟨symm⟩

@[simp] theorem mul_apply {n : ℕ} {U : Set (Affine n)} (a b : Biholomorph U U) (x : U) :
    (a*b).toHomeomorph x=a.toHomeomorph (b.toHomeomorph x) := rfl
@[simp] theorem one_apply {n : ℕ} {U : Set (Affine n)} (x : U) :
    (1 : Biholomorph U U).toHomeomorph x=x := rfl
@[simp] theorem inv_apply {n : ℕ} {U : Set (Affine n)} (a : Biholomorph U U) (x : U) :
    a⁻¹.toHomeomorph x=a.toHomeomorph.symm x := rfl

noncomputable instance automorphismGroup {n : ℕ} {U : Set (Affine n)} : Group (Biholomorph U U) :=
  Group.ofLeftAxioms (fun _ _ _ => ext (fun _ => rfl)) (fun _ => ext (fun _ => rfl))
    (fun a => ext (fun x => a.toHomeomorph.symm_apply_apply x))

def compactOpenPair {n : ℕ} {U : Set (Affine n)} (a : Biholomorph U U) : C(U,U) × C(U,U) :=
  (⟨a.toHomeomorph,a.toHomeomorph.continuous⟩,
   ⟨a.toHomeomorph.symm,a.toHomeomorph.symm.continuous⟩)

instance automorphismTopology {n : ℕ} {U : Set (Affine n)} : TopologicalSpace (Biholomorph U U) :=
  TopologicalSpace.induced compactOpenPair inferInstance

theorem compactOpenPair_injective {n : ℕ} {U : Set (Affine n)} :
    Function.Injective (compactOpenPair (U := U)) := by
  intro a b h
  exact ext (fun x => congrArg (fun p : C(U,U) × C(U,U) => p.1 x) h)

theorem compactOpenPair_isEmbedding {n : ℕ} {U : Set (Affine n)} :
    IsEmbedding (compactOpenPair (U := U)) := compactOpenPair_injective.isEmbedding_induced

theorem continuous_compactOpenPair {n : ℕ} {U : Set (Affine n)} :
    Continuous (compactOpenPair (U := U)) := compactOpenPair_isEmbedding.continuous

instance automorphismMetrizable {n : ℕ} {U : Set (Affine n)}
    [LocallyCompactSpace U] [SigmaCompactSpace U] : MetrizableSpace (Biholomorph U U) :=
  compactOpenPair_isEmbedding.metrizableSpace

instance automorphismTopologicalGroup {n : ℕ} {U : Set (Affine n)}
    [LocallyCompactSpace U] : IsTopologicalGroup (Biholomorph U U) where
  continuous_mul := by
    apply compactOpenPair_isEmbedding.isInducing.continuous_iff.mpr
    have h1 := (ContinuousMap.continuous_comp' (X := U) (Y := U) (Z := U)).comp
      ((continuous_compactOpenPair.fst.comp continuous_snd).prodMk
       (continuous_compactOpenPair.fst.comp continuous_fst))
    have h2 := (ContinuousMap.continuous_comp' (X := U) (Y := U) (Z := U)).comp
      ((continuous_compactOpenPair.snd.comp continuous_fst).prodMk
       (continuous_compactOpenPair.snd.comp continuous_snd))
    exact h1.prodMk h2
  continuous_inv := by
    apply compactOpenPair_isEmbedding.isInducing.continuous_iff.mpr
    exact continuous_compactOpenPair.snd.prodMk continuous_compactOpenPair.fst

theorem continuous_evaluation {n : ℕ} {U : Set (Affine n)} (p : U) :
    Continuous (fun a : Biholomorph U U => a.toHomeomorph p) := by
  change Continuous (fun a : Biholomorph U U => (compactOpenPair a).1 p)
  exact (continuous_eval_const p).comp continuous_compactOpenPair.fst

theorem tendsto_of_ambient_locallyUniformly {n : ℕ} {U : Set (Affine n)}
    [LocallyCompactSpace U] {ι : Type*} {a : ι → Biholomorph U U}
    {e : Biholomorph U U} {l : Filter ι}
    (hf : TendstoLocallyUniformlyOn
      (fun j => ambientExtend (fun x : U => ((a j).toHomeomorph x).val))
      (ambientExtend (fun x : U => (e.toHomeomorph x).val)) l U)
    (hg : TendstoLocallyUniformlyOn
      (fun j => ambientExtend (fun x : U => ((a j).toHomeomorph.symm x).val))
      (ambientExtend (fun x : U => (e.toHomeomorph.symm x).val)) l U) :
    Tendsto a l (𝓝 e) := by
  apply compactOpenPair_isEmbedding.isInducing.tendsto_nhds_iff.mpr
  let v : C(U,Affine n) := ⟨Subtype.val,continuous_subtype_val⟩
  have hv := ContinuousMap.isInducing_postcomp (X := U) v IsEmbedding.subtypeVal.isInducing
  have h1 : Tendsto (fun j => (compactOpenPair (a j)).1) l (𝓝 (compactOpenPair e).1) := by
    apply hv.tendsto_nhds_iff.mpr
    apply ContinuousMap.tendsto_of_tendstoLocallyUniformly
    change TendstoLocallyUniformly (fun j (x : U) => ((a j).toHomeomorph x).val)
      (fun x : U => (e.toHomeomorph x).val) l
    simpa only [Function.comp_def,ambientExtend_apply] using
      tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe.mp hf
  have h2 : Tendsto (fun j => (compactOpenPair (a j)).2) l (𝓝 (compactOpenPair e).2) := by
    apply hv.tendsto_nhds_iff.mpr
    apply ContinuousMap.tendsto_of_tendstoLocallyUniformly
    change TendstoLocallyUniformly (fun j (x : U) => ((a j).toHomeomorph.symm x).val)
      (fun x : U => (e.toHomeomorph.symm x).val) l
    simpa only [Function.comp_def,ambientExtend_apply] using
      tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe.mp hg
  exact h1.prodMk_nhds h2

end Biholomorph
end Release061

end

end OAI
