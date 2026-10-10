import Mathlib
import OAI.MathematicalPhysics.BFSS.FiniteFamilies
import OAI.MathematicalPhysics.BFSS.SharpCutoffs
import OAI.MathematicalPhysics.BFSS.ProfileEnergy

namespace OAI

/-! Closed normal oscillator forms and summed profile energy limits. -/

namespace BFSSNormalAnalysis
noncomputable section
open Set Filter Topology Finset
variable {ι : Type*} [Fintype ι]

lemma finite_nonnegative_energy_subsequence (a : ℕ → ι → ℝ) (C : ℝ)
    (ha : ∀ n i, 0 ≤ a n i) (hb : ∀ n, (∑ i, a n i) ≤ C) :
    ∃ b : ι → ℝ, ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ i, Tendsto (fun n => a (σ n) i) atTop (𝓝 (b i)) := by
  classical
  have hc : IsCompact (Set.pi Set.univ (fun _ : ι => Set.Icc 0 C)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  have hm (n : ℕ) : a n ∈ Set.pi Set.univ (fun _ : ι => Set.Icc 0 C) := by
    intro i hi
    exact ⟨ha n i,(Finset.single_le_sum (fun j _ => ha n j) (Finset.mem_univ i)).trans (hb n)⟩
  obtain ⟨b,hb,σ,hσ,ht⟩ := hc.tendsto_subseq hm
  exact ⟨b,σ,hσ,fun i => (tendsto_pi_nhds.mp ht) i⟩
end
end BFSSNormalAnalysis

namespace BFSSQuantum.AlgebraData
noncomputable section
open scoped NNReal
open MeasureTheory
variable {N : ℕ} (M : AlgebraData N)

abbrev NormalGradient (q : Boson N) :=
  BFSSSliceSobolev.Gradient (F := Fermion N) (volume : Measure (M.NormalCoordinates q))
    (ι := Fin (Module.finrank ℝ (M.normalSlice q)))

def normalOscillatorForm (q : Boson N)
    (u : Lp (Fermion N) 2 (volume : Measure (M.NormalCoordinates q)))
    (v : M.NormalGradient q) : ℝ :=
  (1/2 : ℝ)*‖v‖^2 +
    (∫ x : M.NormalCoordinates q, M.normalQuadratic q (M.normalCoordinateIsometry q x : Boson N)*‖u x‖^2) +
    (∫ x : M.NormalCoordinates q, inner ℝ (u x) (M.deformedFermionField 1 1 q (u x)))

def NormalFormDomain (q : Boson N)
    (u : Lp (Fermion N) 2 (volume : Measure (M.NormalCoordinates q)))
    (v : M.NormalGradient q) : Prop :=
  (u,v) ∈ BFSSSliceSobolev.closedGraph volume
    (EuclideanSpace.basisFun (Fin (Module.finrank ℝ (M.normalSlice q))) ℝ) ∧
  MemLp (fun x : M.NormalCoordinates q =>
    Real.sqrt (M.normalQuadratic q (M.normalCoordinateIsometry q x : Boson N)) • u x) 2 volume

lemma normalPotential_norm_sq (q : Boson N)
    (u : Lp (Fermion N) 2 (volume : Measure (M.NormalCoordinates q)))
    (hm : MemLp (fun x : M.NormalCoordinates q =>
      Real.sqrt (M.normalQuadratic q (M.normalCoordinateIsometry q x : Boson N)) • u x) 2 volume) :
    ‖hm.toLp (fun x => Real.sqrt (M.normalQuadratic q (M.normalCoordinateIsometry q x : Boson N)) • u x)‖^2 =
      ∫ x : M.NormalCoordinates q, M.normalQuadratic q (M.normalCoordinateIsometry q x : Boson N)*‖u x‖^2 := by
  rw [←real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hm.coeFn_toLp] with x hx
  rw [hx,real_inner_self_eq_norm_sq,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,
    Real.sq_sqrt (M.normalQuadratic_nonneg q _)]
end
end BFSSQuantum.AlgebraData

namespace BFSSQuantum.AlgebraData.GaugeData.MeasuredNormalPatch
noncomputable section
open scoped NNReal
open MeasureTheory Set Filter Topology
variable {N : ℕ} {M : AlgebraData N} {G : M.GaugeData} {q : Boson N}
variable (P : G.MeasuredNormalPatch q)
attribute [local irreducible] AlgebraData.normalSlice AlgebraData.gaugeAction coreToL2
local instance oscillatorLimitsPatchFermionInnerProductSpace : InnerProductSpace ℝ (Fermion N) := inferInstance
local instance oscillatorLimitsPatchFermionCompleteSpace : CompleteSpace (Fermion N) := inferInstance

def ambientKinetic (h : ℝ) (f : G.invariantCore) : ℝ :=
  ∫ x, P.cutoff (h • x)*kineticDensity f.val x

def profileBosonicEnergy (h : ℝ) (f : G.invariantCore) : ℝ :=
  ∫ x : M.NormalCoordinates q, M.normalEffectivePotential q h
    (M.normalCoordinateIsometry q x : Boson N)*‖P.profile h f x‖^2

def profileFermionicEnergy (h : ℝ) (f : G.invariantCore) : ℝ :=
  ∫ x : M.NormalCoordinates q, inner ℝ (P.profile h f x)
    (M.deformedFermionField h 1 (h⁻¹ • q+(M.normalCoordinateIsometry q x : Boson N)) (P.profile h f x))

lemma ambientKinetic_nonneg (h : ℝ) (f : G.invariantCore) : 0 ≤ P.ambientKinetic h f :=
  integral_nonneg (fun x => mul_nonneg (P.cutoff_bounds _).1 (kineticDensity_nonneg f.val x))

lemma profileBosonicEnergy_nonneg (h : ℝ) (f : G.invariantCore) : 0 ≤ P.profileBosonicEnergy h f :=
  integral_nonneg (fun _ => mul_nonneg (M.normalEffectivePotential_nonneg q h _) (sq_nonneg _))

lemma ambientEnergy_components (hN : 2 ≤ N) (hq : q ∈ M.massiveZeros)
    {h : ℝ} (hh : 0 < h) (f : G.invariantCore) :
    P.ambientEnergy h f = (1/2 : ℝ)*P.ambientKinetic h f +
      P.profileBosonicEnergy h f + P.profileFermionicEnergy h f :=
  P.ambientEnergy_profile_eq hN hq hh f

theorem profile_oscillator_le_limits (hN : 2 ≤ N) (h : ℕ → ℝ)
    (hh : ∀ n, 0 < h n ∧ h n ≤ 1) (hzero : Tendsto h atTop (𝓝 0))
    (f : ℕ → G.invariantCore) (E : ℝ≥0)
    (hnorm : ∀ n, ‖coreToL2 (f n).val‖^2 ≤ E)
    (henergy : ∀ n, M.deformedCoreEnergy (h n) 1 (f n).val ≤ E)
    (u : Lp (Fermion N) 2 (volume : Measure (M.NormalCoordinates q)))
    (hu : Tendsto (fun n => P.profile (h n) (f n)) atTop (𝓝 u))
    (k₀ b₀ : ℝ)
    (hk : Tendsto (fun n => P.ambientKinetic (h n) (f n)) atTop (𝓝 k₀))
    (hb : Tendsto (fun n => P.profileBosonicEnergy (h n) (f n)) atTop (𝓝 b₀)) :
    ∃ v : M.NormalGradient q, M.NormalFormDomain q u v ∧
      M.normalOscillatorForm q u v ≤ (1/2 : ℝ)*k₀+b₀+
        (∫ x : M.NormalCoordinates q, inner ℝ (u x) (M.deformedFermionField 1 1 q (u x))) := by
  obtain ⟨v,hv⟩ := P.profile_limit_gradient hN h hh hzero f E hnorm henergy u hu
  obtain ⟨hm,hmb⟩ := P.profile_bosonic_energy_le_limit h hzero f u hu b₀ hb
  have hg := P.profile_gradient_add_le_limit hN h hh hzero f E hnorm u hu v hv
    (fun _ => 0) 0 k₀ tendsto_const_nhds (by simpa only [ambientKinetic,add_zero] using hk)
  rw [M.normalPotential_norm_sq q u hm] at hmb
  refine ⟨v,⟨hv,hm⟩,?_⟩
  dsimp only [AlgebraData.normalOscillatorForm]
  linarith only [hg,hmb]
end
end BFSSQuantum.AlgebraData.GaugeData.MeasuredNormalPatch

namespace BFSSQuantum.AlgebraData.GaugeData
noncomputable section
open scoped NNReal
open MeasureTheory Finset Set Filter Topology
variable {N : ℕ} {M : AlgebraData N} (G : M.GaugeData)
variable {ι : Type*} [Fintype ι] (q : ι → Boson N) (P : (i : ι) → G.MeasuredNormalPatch (q i))
attribute [local irreducible] AlgebraData.normalSlice AlgebraData.gaugeAction coreToL2
local instance oscillatorLimitsFamilyFermionInnerProductSpace : InnerProductSpace ℝ (Fermion N) := inferInstance
local instance oscillatorLimitsFamilyFermionCompleteSpace : CompleteSpace (Fermion N) := inferInstance

theorem normalPatch_summed_energy_limit (hN : 2 ≤ N)
    (hq : ∀ i, q i ∈ M.massiveZeros)
    (hd : Pairwise (fun i j => Disjoint (Function.support (P i).cutoff) (Function.support (P j).cutoff)))
    (h : ℕ → ℝ) (hh : ∀ n, 0 < h n ∧ h n ≤ 1) (hzero : Tendsto h atTop (𝓝 0))
    (f : ℕ → G.invariantCore) (E : ℝ≥0)
    (hnorm : ∀ n, ‖coreToL2 (f n).val‖^2 ≤ E)
    (henergy : ∀ n, M.deformedCoreEnergy (h n) 1 (f n).val ≤ E)
    (u : (i : ι) → Lp (Fermion N) 2 (volume : Measure (M.NormalCoordinates (q i))))
    (hu : ∀ i, Tendsto (fun n => (P i).profile (h n) (f n)) atTop (𝓝 (u i)))
    (hdeficit : Tendsto (fun n => ‖coreToL2 (f n).val‖^2 -
      ∑ i, ‖(P i).profile (h n) (f n)‖^2) atTop (𝓝 0))
    (L : ℝ) (hL : Tendsto (fun n => M.deformedCoreEnergy (h n) 1 (f n).val) atTop (𝓝 L)) :
    ∃ v : (i : ι) → M.NormalGradient (q i),
      (∀ i, M.NormalFormDomain (q i) (u i) (v i)) ∧
      (∑ i, M.normalOscillatorForm (q i) (u i) (v i)) ≤ L := by
  classical
  let F : ι → ℝ := fun i => ∫ x : M.NormalCoordinates (q i),
    inner ℝ (u i x) (M.deformedFermionField 1 1 (q i) (u i x))
  have hF (i : ι) : Tendsto (fun n => (P i).profileFermionicEnergy (h n) (f n)) atTop (𝓝 (F i)) :=
    (P i).profile_fermion_energy_tendsto h hh hzero f E hnorm henergy (u i) (hu i)
  have hFs : Tendsto (fun n => ∑ i, (P i).profileFermionicEnergy (h n) (f n)) atTop (𝓝 (∑ i, F i)) :=
    tendsto_finsetSum _ (fun i _ => hF i)
  obtain ⟨B,hB⟩ := hFs.bddBelow_range
  obtain ⟨K,hK,hcompare⟩ := G.normalPatch_energy_comparison q P hN hd
  let A : ℕ → (ι ⊕ ι) → ℝ := fun n => Sum.elim
    (fun i => (1/2 : ℝ)*(P i).ambientKinetic (h n) (f n))
    (fun i => (P i).profileBosonicEnergy (h n) (f n))
  have hA (n : ℕ) (i : ι ⊕ ι) : 0 ≤ A n i := by
    cases i with
    | inl i => exact mul_nonneg (by norm_num) ((P i).ambientKinetic_nonneg _ _)
    | inr i => exact (P i).profileBosonicEnergy_nonneg _ _
  have hb (n : ℕ) : (∑ i, A n i) ≤ (E : ℝ)+K*E-B := by
    have hsum : 0 ≤ ∑ i, ‖(P i).profile (h n) (f n)‖^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have hdE : ‖coreToL2 (f n).val‖^2 - ∑ i, ‖(P i).profile (h n) (f n)‖^2 ≤ E := by
      linarith only [hnorm n,hsum]
    have hc := (hcompare (h n) (hh n).1 (hh n).2 (f n)).trans
      (add_le_add (henergy n) (mul_le_mul_of_nonneg_left hdE hK))
    have hfB : B ≤ ∑ i, (P i).profileFermionicEnergy (h n) (f n) := hB (mem_range_self n)
    simp_rw [(P _).ambientEnergy_components hN (hq _) (hh n).1] at hc
    simp only [Finset.sum_add_distrib] at hc
    simp only [A,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr]
    linarith only [hc,hfB]
  obtain ⟨a,σ,hσ,ha⟩ := BFSSNormalAnalysis.finite_nonnegative_energy_subsequence A _ hA hb
  have hk (i : ι) : Tendsto (fun n => (P i).ambientKinetic (h (σ n)) (f (σ n))) atTop
      (𝓝 (2*a (Sum.inl i))) := by
    have ht := (ha (Sum.inl i)).const_mul 2
    convert ht using 1
    simp [A]
  have hv (i : ι) := (P i).profile_oscillator_le_limits hN (fun n => h (σ n))
    (fun n => hh (σ n)) (hzero.comp hσ.tendsto_atTop) (fun n => f (σ n)) E
    (fun n => hnorm (σ n)) (fun n => henergy (σ n)) (u i) ((hu i).comp hσ.tendsto_atTop)
    (2*a (Sum.inl i)) (a (Sum.inr i)) (hk i) (ha (Sum.inr i))
  choose v hvD hvE using hv
  refine ⟨v,hvD,?_⟩
  have hsumlim : Tendsto (fun n => ∑ i, (P i).ambientEnergy (h (σ n)) (f (σ n))) atTop
      (𝓝 (∑ i, (a (Sum.inl i)+a (Sum.inr i)+F i))) := by
    simp_rw [(P _).ambientEnergy_components hN (hq _) (hh (σ _)).1]
    apply tendsto_finsetSum
    intro i hi
    exact ((ha (Sum.inl i)).add (ha (Sum.inr i))).add ((hF i).comp hσ.tendsto_atTop)
  have hup : Tendsto (fun n => M.deformedCoreEnergy (h (σ n)) 1 (f (σ n)).val +
      K*(‖coreToL2 (f (σ n)).val‖^2 - ∑ i, ‖(P i).profile (h (σ n)) (f (σ n))‖^2)) atTop (𝓝 L) := by
    simpa using (hL.comp hσ.tendsto_atTop).add ((hdeficit.comp hσ.tendsto_atTop).const_mul K)
  have hLE : (∑ i, (a (Sum.inl i)+a (Sum.inr i)+F i)) ≤ L :=
    le_of_tendsto_of_tendsto hsumlim hup (Filter.Eventually.of_forall
      (fun n => hcompare (h (σ n)) (hh (σ n)).1 (hh (σ n)).2 (f (σ n))))
  apply le_trans (Finset.sum_le_sum (fun i _ => hvE i))
  have he : (∑ i, ((1/2 : ℝ)*(2*a (Sum.inl i))+a (Sum.inr i)+F i)) =
      ∑ i, (a (Sum.inl i)+a (Sum.inr i)+F i) := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  change (∑ i, ((1/2 : ℝ)*(2*a (Sum.inl i))+a (Sum.inr i)+F i)) ≤ L
  rw [he]
  exact hLE
end
end BFSSQuantum.AlgebraData.GaugeData
namespace BFSSQuantum
noncomputable section
open Finset
variable {N : ℕ}

lemma jointEnergy_distance_le (x y : SpinIndex → FullL2 N) {C ε : ℝ}
    (hε : 0 ≤ ε) (hx : ∀ α, ‖x α‖ ≤ C) (hy : ∀ α, ‖y α‖ ≤ C)
    (hd : ∀ α, dist (x α) (y α) ≤ ε) :
    dist (jointEnergy x) (jointEnergy y) ≤ ε*(2*C) := by
  have hb (α : SpinIndex) : dist (‖x α‖^2) (‖y α‖^2) ≤ ε*(2*C) := by
    apply (BFSSRellich.normSquare_distance_le (x α) (y α)).trans
    apply mul_le_mul (hd α) _ (add_nonneg (norm_nonneg _) (norm_nonneg _)) hε
    linarith [hx α,hy α]
  change dist ((1/16 : ℝ)*∑ α, ‖x α‖^2) ((1/16 : ℝ)*∑ α, ‖y α‖^2) ≤ _
  rw [Real.dist_eq, ←mul_sub, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/16), ←Real.dist_eq]
  have hs := (dist_sum_sum_le Finset.univ (fun α => ‖x α‖^2) (fun α => ‖y α‖^2)).trans
    (Finset.sum_le_sum (fun α _ => hb α))
  have hm := mul_le_mul_of_nonneg_left hs (by norm_num : (0:ℝ) ≤ 1/16)
  norm_num [SpinIndex] at hm
  nlinarith [hm]
end
end BFSSQuantum

end OAI
