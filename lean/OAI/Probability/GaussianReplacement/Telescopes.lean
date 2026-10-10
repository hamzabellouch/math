import OAI.Probability.GaussianReplacement.ArrayBounds

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace
open InformationTheory


lemma averaged_telescope_block {m a b : ℕ} (hab : a ≤ b)
    (J T : ℕ → ℕ → ℝ) (K : ℕ → ℝ) (C S B q : ℝ) (hq : 0 < q)
    (hstep : ∀ i < m, ∀ k ∈ Finset.Icc a b,
      J i k-J (i+1) k ≤ C+K i/q+T i (k+1)-T i k)
    (hfirst : ∀ i < m, 0 ≤ T i a)
    (hlast : ∀ i < m, T i (b+1) ≤ S)
    (hK : ∑ i ∈ Finset.range m, K i ≤ B) :
    (∑ k ∈ Finset.Icc a b, J 0 k)/(b-a+1:ℕ) -
      (∑ k ∈ Finset.Icc a b, J m k)/(b-a+1:ℕ) ≤
        C*m+(m:ℝ)/(b-a+1:ℕ)*S+B/q := by
  let N : ℝ := (b-a+1:ℕ)
  have hN : 0 < N := by dsimp [N]; positivity
  have hcard : ((Finset.Icc a b).card:ℝ) = N := by
    dsimp [N]
    simp only [Nat.card_Icc]
    congr 1
    omega
  have he : Finset.Icc a b = Finset.Ico a (b+1) := by
    ext k
    simp only [Finset.mem_Icc,Finset.mem_Ico]
    omega
  have hs (i : ℕ) : ∑ k ∈ Finset.Icc a b, (T i (k+1)-T i k) = T i (b+1)-T i a := by
    rw [he]
    exact Finset.sum_Ico_sub _ (by omega)
  let F : ℕ → ℝ := fun i => (∑ k ∈ Finset.Icc a b, J i k)/N
  have hrow (i : ℕ) (hi : i < m) : F i-F (i+1) ≤ C+S/N+K i/q := by
    have h := Finset.sum_le_sum (fun k hk => hstep i hi k hk)
    have hrepr : ∑ k ∈ Finset.Icc a b, (C+K i/q+T i (k+1)-T i k) =
        N*(C+K i/q)+T i (b+1)-T i a := by
      simp_rw [show ∀ k, C+K i/q+T i (k+1)-T i k = (C+K i/q)+(T i (k+1)-T i k) by intro k; ring]
      rw [Finset.sum_add_distrib,hs,Finset.sum_const,nsmul_eq_mul,hcard]
      ring
    rw [hrepr,Finset.sum_sub_distrib] at h
    dsimp only [F]
    rw [←sub_div]
    apply (div_le_iff₀ hN).mpr
    have hfirst' := hfirst i hi
    have hlast' := hlast i hi
    calc
      _ ≤ N*(C+K i/q)+S := by linarith
      _ = (C+S/N+K i/q)*N := by field_simp; ring
  have hsum := Finset.sum_le_sum (fun i hi => hrow i (Finset.mem_range.mp hi))
  rw [Finset.sum_range_sub'] at hsum
  have hsumr : ∑ i ∈ Finset.range m, (C+S/N+K i/q) =
      (m:ℝ)*(C+S/N)+(∑ i ∈ Finset.range m, K i)/q := by
    rw [Finset.sum_add_distrib,Finset.sum_div,Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  rw [hsumr] at hsum
  have hKq := div_le_div_of_nonneg_right hK hq.le
  change F 0-F m ≤ C*m+(m:ℝ)/N*S+B/q
  calc
    _ ≤ (m:ℝ)*(C+S/N)+(∑ i ∈ Finset.range m, K i)/q := hsum
    _ ≤ (m:ℝ)*(C+S/N)+B/q := add_le_add_right hKq _
    _ = _ := by ring



lemma prefix_charge_sum {d m : ℕ} {W : Type*} [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W]
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P]
    (hd : 1 ≤ d) (hInd : (P.map swapLast).fst = (uniformSphere d).prod (gaussianRows m d))
    {B : ℝ} (hB : 0 ≤ B) (hH : shannonEntropy P.fst.snd ≤ ENNReal.ofReal B) :
    (∑ i ∈ Finset.range m, (if hi : i < m then
      (klDiv (nextActualRowLaw P i hi) ((nextActualRowLaw P i hi).fst.prod (stdGaussian (Vector d)))).toReal else 0)) ≤ B := by
  classical
  let : IsProbabilityMeasure (uniformSphere d) := uniformSphere_probability_of_pos hd
  let R : ℕ → ℝ := fun i => if hi : i ≤ m then
    (rowInformation (prefixLaw P i hi) (gaussianRows i d)).toReal else 0
  have hR (i : ℕ) (hi : i ≤ m) := rowInformation_finite_bound (prefixLaw P i hi) hd
    (prefixLaw_independence P (uniformSphere d) hInd i hi) hB (by rwa [prefixLaw_fst])
  have hstep (i : ℕ) (hi : i < m) :
      (klDiv (nextActualRowLaw P i hi) ((nextActualRowLaw P i hi).fst.prod (stdGaussian (Vector d)))).toReal = R (i+1)-R i := by
    have he := prefix_rowInformation_step P i hi
    have hK : klDiv (nextActualRowLaw P i hi) ((nextActualRowLaw P i hi).fst.prod (stdGaussian (Vector d))) ≠ ∞ :=
      ne_top_of_le_ne_top (hR (i+1) (by omega)).1 (by rw [he]; exact le_add_left le_rfl)
    have her := congrArg ENNReal.toReal he
    rw [ENNReal.toReal_add (hR i (by omega)).1 hK] at her
    simp only [R,dite_eq_left (Nat.le_of_lt hi),dite_eq_left (Nat.succ_le_of_lt hi)]
    linarith
  have he : (∑ i ∈ Finset.range m, (if hi : i < m then
      (klDiv (nextActualRowLaw P i hi) ((nextActualRowLaw P i hi).fst.prod (stdGaussian (Vector d)))).toReal else 0)) = R m-R 0 := by
    calc
      _ = ∑ i ∈ Finset.range m, (R (i+1)-R i) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [dite_eq_left (Finset.mem_range.mp hi),hstep i (Finset.mem_range.mp hi)]
      _ = _ := Finset.sum_range_sub R m
  rw [he]
  have h0 : 0 ≤ R 0 := by simp only [R,dite_eq_left (Nat.zero_le m)]; exact ENNReal.toReal_nonneg
  have hm : R m ≤ B := by simp only [R,dite_eq_left le_rfl]; exact (hR m le_rfl).2
  linarith

lemma hybrid_average_ending {d m : ℕ} {W : Type*}
    [MeasurableSpace W] [StandardBorelSpace W] [Nonempty W]
    [Countable W] [MeasurableSingletonClass W]
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P]
    (hd : 256 ≤ d) (hm : m ≤ d/8)
    (hInd : (P.map swapLast).fst = (uniformSphere d).prod (gaussianRows m d))
    {B : ℝ} (hB : 0 ≤ B) (hH : shannonEntropy P.fst.snd ≤ ENNReal.ofReal B) :
    (∑ k ∈ Finset.Icc (hybridFirst d) (hybridLast d),
      (exposedInformation (alignedExperiment (r:=k) (prefixLaw P 0 (Nat.zero_le m)))).toReal)/hybridCount d -
    (∑ k ∈ Finset.Icc (hybridFirst d) (hybridLast d),
      (exposedInformation (alignedExperiment (r:=k-m) P)).toReal)/hybridCount d ≤
      hybridRowConstant*m + (m:ℝ)/hybridCount d*(16*hybridBaselineConstant+B/(d/8:ℕ))+B/(d/32:ℕ) := by
  classical
  let : IsProbabilityMeasure (uniformSphere d) := uniformSphere_probability_of_pos (by omega)
  let J : ℕ → ℕ → ℝ := fun i k => if hi : i ≤ m then
    (exposedInformation (alignedExperiment (r:=k-i) (prefixLaw P i hi))).toReal else 0
  let T : ℕ → ℕ → ℝ := fun i k => if hi : i ≤ m then
    (freshSlope (observationSignalLaw (prefixLaw P i hi)) (k-i-1)).toReal else 0
  let K : ℕ → ℝ := fun i => if hi : i < m then
    (klDiv (nextActualRowLaw P i hi) ((nextActualRowLaw P i hi).fst.prod (stdGaussian (Vector d)))).toReal else 0
  have hab : hybridFirst d ≤ hybridLast d := by unfold hybridFirst hybridLast; omega
  have hstep (i : ℕ) (hi : i < m) (k : ℕ) (hk : k ∈ Finset.Icc (hybridFirst d) (hybridLast d)) :
      J i k-J (i+1) k ≤ hybridRowConstant+K i/(d/32:ℕ)+T i (k+1)-T i k := by
    obtain ⟨hka,hkb⟩ := Finset.mem_Icc.mp hk
    dsimp [hybridFirst,hybridLast] at hka hkb
    have h := hybrid_one_step (r:=k-(i+1)) (q:=d/32) P (by omega) hInd hB hH hi
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    simp only [J,T,K,dite_eq_left (Nat.le_of_lt hi),dite_eq_left (Nat.succ_le_of_lt hi),dite_eq_left hi]
    have hsub0 : k-i = k-(i+1)+1 := by omega
    have hsub1 : k+1-i-1 = k-(i+1)+1 := by omega
    have hsub2 : k-i-1 = k-(i+1) := by omega
    rw [hsub1,hsub2,hsub0]
    exact h
  have hfirst (i : ℕ) (hi : i < m) : 0 ≤ T i (hybridFirst d) := by
    simp only [T,dite_eq_left (Nat.le_of_lt hi)]
    exact ENNReal.toReal_nonneg
  have hlast (i : ℕ) (hi : i < m) : T i (hybridLast d+1) ≤ 16*hybridBaselineConstant+B/(d/8:ℕ) := by
    simp only [T,dite_eq_left (Nat.le_of_lt hi)]
    apply (freshSlope_from_array_bound (prefixLaw P i (Nat.le_of_lt hi)) (by omega)
      (prefixLaw_independence P (uniformSphere d) hInd i _) hB (by rwa [prefixLaw_fst]) ?_ ?_).2
    · unfold hybridLast; omega
    · unfold hybridLast; omega
  have hsum := averaged_telescope_block hab J T K hybridRowConstant
    (16*hybridBaselineConstant+B/(d/8:ℕ)) B (d/32:ℕ) (by exact_mod_cast (show 0 < d/32 by omega))
      hstep hfirst hlast (prefix_charge_sum P (by omega) hInd hB hH)
  simpa only [J,dite_eq_left (Nat.zero_le m),dite_eq_left le_rfl,Nat.sub_zero,prefixLaw_self,hybridCount] using hsum



def processedKernel {Z A B C : Type*} [MeasurableSpace Z] [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C] (α : Kernel Z (A×B))
    (η : Kernel (Z×B) C) : Kernel Z (A×C) :=
  (α ⊗ₖ η.comap (Prod.map id Prod.snd) (measurable_id.prodMap measurable_snd)).map
    (fun z => (z.1.1,z.2))

instance processedKernel_markov {Z A B C : Type*} [MeasurableSpace Z] [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C] (α : Kernel Z (A×B)) [IsMarkovKernel α]
    (η : Kernel (Z×B) C) [IsMarkovKernel η] : IsMarkovKernel (processedKernel α η) := by
  unfold processedKernel
  exact Kernel.IsMarkovKernel.map _ (measurable_fst.fst.prodMk measurable_snd)

lemma processedKernel_apply_prod {Z A B C : Type*} [MeasurableSpace Z] [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C] (α : Kernel Z (A×B)) [IsMarkovKernel α]
    (η : Kernel (Z×B) C) [IsMarkovKernel η] (z : Z)
    {s : Set A} {t : Set C} (hs : MeasurableSet s) (ht : MeasurableSet t) :
    processedKernel α η z (s×ˢt) = ∫⁻ p in s×ˢSet.univ, η (z,p.2) t ∂α z := by
  rw [processedKernel,Kernel.map_apply _ (measurable_fst.fst.prodMk measurable_snd),Measure.map_apply (measurable_fst.fst.prodMk measurable_snd) (hs.prod ht)]
  rw [show (fun p : (A×B)×C => (p.1.1,p.2)) ⁻¹' (s×ˢt) = (s×ˢSet.univ)×ˢt by ext p; simp]
  rw [Kernel.compProd_apply_prod (hs.prod MeasurableSet.univ) ht]
  rfl

lemma processedKernel_fst {Z A B C : Type*} [MeasurableSpace Z] [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C] (α : Kernel Z (A×B)) [IsMarkovKernel α]
    (η : Kernel (Z×B) C) [IsMarkovKernel η] : (processedKernel α η).fst = α.fst := by
  rw [processedKernel,Kernel.fst_eq,←Kernel.map_comp_right _ (measurable_fst.fst.prodMk measurable_snd) measurable_fst]
  change (α ⊗ₖ η.comap (Prod.map id Prod.snd) (measurable_id.prodMap measurable_snd)).map (Prod.fst ∘ Prod.fst) = _
  rw [Kernel.map_comp_right _ measurable_fst measurable_fst]
  rw [←Kernel.fst_eq,←Kernel.fst_eq,Kernel.fst_compProd]

lemma processedKernel_snd_apply {Z A B C : Type*} [MeasurableSpace Z] [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C] (α : Kernel Z (A×B)) [IsMarkovKernel α]
    (η : Kernel (Z×B) C) [IsMarkovKernel η] (z : Z) {t : Set C} (ht : MeasurableSet t) :
    (processedKernel α η).snd z t = ∫⁻ b, η (z,b) t ∂α.snd z := by
  rw [Kernel.snd_apply' _ _ ht]
  rw [show (Prod.snd : A×C → C) ⁻¹' t = Set.univ×ˢt by ext p; simp]
  rw [processedKernel_apply_prod α η z MeasurableSet.univ ht]
  simp only [Set.univ_prod_univ,Measure.restrict_univ]
  rw [Kernel.snd_eq,Kernel.map_apply _ measurable_snd]
  rw [lintegral_map (by exact (η.measurable_coe ht).comp (measurable_const.prodMk measurable_id)) measurable_snd]

lemma processedKernel_reference {Z A B C : Type*} [MeasurableSpace Z] [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C] (α : Kernel Z (A×B)) [IsMarkovKernel α]
    (η : Kernel (Z×B) C) [IsMarkovKernel η] :
    processedKernel (α.fst ×ₖ α.snd) η = (processedKernel α η).fst ×ₖ (processedKernel α η).snd := by
  rw [processedKernel_fst]
  ext z : 1
  apply Measure.ext_prod
  intro s t hs ht
  rw [processedKernel_apply_prod _ _ _ hs ht,Kernel.prod_apply_prod,processedKernel_snd_apply _ _ _ ht,
    Kernel.prod_apply,←Measure.prod_restrict (s:=s) (t:=Set.univ),Measure.restrict_univ]
  rw [lintegral_prod _ (by exact ((η.measurable_coe ht).comp (measurable_const.prodMk measurable_snd)).aemeasurable)]
  simp only [lintegral_const,Measure.restrict_apply_univ]
  rw [mul_comm]

lemma compProd_processedKernel {Z A B C : Type*} [MeasurableSpace Z] [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C] (μ : Measure Z) [IsFiniteMeasure μ]
    (α : Kernel Z (A×B)) [IsMarkovKernel α] (η : Kernel (Z×B) C) [IsMarkovKernel η] :
    μ ⊗ₘ processedKernel α η =
      ((μ ⊗ₘ α) ⊗ₘ η.comap (Prod.map id Prod.snd) (measurable_id.prodMap measurable_snd)).map
        (fun z => (z.1.1,(z.1.2.1,z.2))) := by
  rw [processedKernel,Measure.compProd_map (measurable_fst.fst.prodMk measurable_snd),
    ←Measure.compProd_assoc,Measure.map_map
      (measurable_fst.fst.prodMk (measurable_fst.snd.fst.prodMk measurable_snd))
      MeasurableEquiv.prodAssoc.symm.measurable]
  rfl

lemma conditionalMutualInformation_processedKernel_le {Z A B C : Type*}
    [MeasurableSpace Z] [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    [StandardBorelSpace A] [StandardBorelSpace B] [StandardBorelSpace C]
    [Nonempty A] [Nonempty B] [Nonempty C]
    (μ : Measure Z) [IsProbabilityMeasure μ]
    (α : Kernel Z (A×B)) [IsMarkovKernel α] (η : Kernel (Z×B) C) [IsMarkovKernel η] :
    conditionalMutualInformation (μ ⊗ₘ processedKernel α η) ≤ conditionalMutualInformation (μ ⊗ₘ α) := by
  rw [conditionalMutualInformation_compProd,conditionalMutualInformation_compProd,
    ←processedKernel_reference,compProd_processedKernel,compProd_processedKernel]
  calc
    _ ≤ klDiv ((μ ⊗ₘ α) ⊗ₘ η.comap (Prod.map id Prod.snd) (measurable_id.prodMap measurable_snd))
      ((μ ⊗ₘ (α.fst ×ₖ α.snd)) ⊗ₘ η.comap (Prod.map id Prod.snd) (measurable_id.prodMap measurable_snd)) :=
      klDiv_map_le _ _ (measurable_fst.fst.prodMk (measurable_fst.snd.fst.prodMk measurable_snd))
    _ = _ := klDiv_compProd_left _ _ _

def processedLaw {Z A B C : Type*} [MeasurableSpace Z] [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C] (P : Measure (Z×(A×B)))
    (η : Kernel (Z×B) C) : Measure (Z×(A×C)) :=
  (P ⊗ₘ η.comap (Prod.map id Prod.snd) (measurable_id.prodMap measurable_snd)).map
    (fun z => (z.1.1,(z.1.2.1,z.2)))

instance processedLaw_probability {Z A B C : Type*} [MeasurableSpace Z] [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C] (P : Measure (Z×(A×B))) [IsProbabilityMeasure P]
    (η : Kernel (Z×B) C) [IsMarkovKernel η] : IsProbabilityMeasure (processedLaw P η) := by
  exact (Measure.isProbabilityMeasure_map_iff
    (measurable_fst.fst.prodMk (measurable_fst.snd.fst.prodMk measurable_snd)).aemeasurable).mpr
    inferInstance

lemma conditionalMutualInformation_processed_le {Z A B C : Type*}
    [MeasurableSpace Z] [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    [StandardBorelSpace A] [StandardBorelSpace B] [StandardBorelSpace C]
    [Nonempty A] [Nonempty B] [Nonempty C]
    (P : Measure (Z×(A×B))) [IsProbabilityMeasure P] (η : Kernel (Z×B) C) [IsMarkovKernel η] :
    conditionalMutualInformation (processedLaw P η) ≤ conditionalMutualInformation P := by
  have h := conditionalMutualInformation_processedKernel_le P.fst P.condKernel η
  simpa only [compProd_processedKernel,P.disintegrate P.condKernel,processedLaw] using h



lemma compProd_map_base {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] (μ : Measure A) [IsProbabilityMeasure μ]
    (κ : Kernel B C) [IsMarkovKernel κ] (f : A → B) (hf : Measurable f) :
    μ.map f ⊗ₘ κ = (μ ⊗ₘ κ.comap f hf).map (Prod.map f id) := by
  apply Measure.ext_prod
  intro s t hs ht
  rw [Measure.compProd_apply_prod hs ht,Measure.map_apply (hf.prodMap measurable_id) (hs.prod ht)]
  change _ = (μ ⊗ₘ κ.comap f hf) ((f ⁻¹' s)×ˢt)
  rw [Measure.compProd_apply_prod (hs.preimage hf) ht,setLIntegral_map hs (κ.measurable_coe ht) hf]
  rfl

lemma compProd_independent_swap {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] (μ : Measure A) [IsProbabilityMeasure μ]
    (κ : Kernel A B) [IsMarkovKernel κ] (γ : Measure C) [IsProbabilityMeasure γ] :
    ((μ ⊗ₘ κ).prod γ).map (fun z => ((z.1.1,z.2),z.1.2)) =
      (μ.prod γ) ⊗ₘ κ.comap Prod.fst measurable_fst := by
  apply Measure.ext_prod₃'
  intro s t u hs ht hu
  rw [Measure.map_apply ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd) ((hs.prod ht).prod hu)]
  have he : (fun z : (A×B)×C => ((z.1.1,z.2),z.1.2)) ⁻¹' ((s×ˢt)×ˢu) = (s×ˢu)×ˢt := by
    ext z; simp only [Set.mem_preimage,Set.mem_prod]; tauto
  rw [he,Measure.prod_prod,Measure.compProd_apply_prod hs hu,Measure.compProd_apply_prod (hs.prod ht) hu,
    ←Measure.prod_restrict,lintegral_prod _ (by exact ((κ.measurable_coe hu).comp measurable_fst).aemeasurable)]
  simp only [Kernel.comap_apply,lintegral_const,Measure.restrict_apply_univ]
  rw [lintegral_mul_const _ (κ.measurable_coe hu)]

lemma probability_prod_subsingleton {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [Subsingleton B] (μ : Measure (A×B)) [IsProbabilityMeasure μ]
    (γ : Measure B) [IsProbabilityMeasure γ] : μ = μ.fst.prod γ := by
  apply Measure.ext_prod
  intro s t hs ht
  by_cases ht0 : t = ∅
  · simp [ht0]
  · have ht1 : t = Set.univ := (Set.nonempty_iff_ne_empty.mpr ht0).eq_univ
    rw [ht1,Measure.prod_prod,measure_univ,mul_one]
    rw [Measure.fst_apply hs]
    congr 1
    ext z; simp

lemma alignedExperiment_fresh {d m r : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure (Sphere d×W)) [IsProbabilityMeasure P] :
    alignedExperiment (r:=r) (P.prod (gaussianRows m d)) = P.prod (gaussianRows (m+r) d) := by
  change Measure.map ((Prod.map id (fun p : Rows m d×Rows r d => Fin.append p.1 p.2)) ∘
    MeasurableEquiv.prodAssoc) ((P.prod (gaussianRows m d)).prod (gaussianRows r d)) = _
  rw [←Measure.map_map (measurable_id.prodMap (measurable_append (E:=Vector d) m r))
    MeasurableEquiv.prodAssoc.measurable,Measure.prodAssoc_prod,
    ←Measure.map_prod_map _ _ measurable_id (measurable_append (E:=Vector d) m r),Measure.map_id]
  rw [show ((gaussianRows m d).prod (gaussianRows r d)).map (fun p => Fin.append p.1 p.2) =
    gaussianRows (m+r) d from map_append_pi (stdGaussian (Vector d)) m r]

lemma exposedInformation_prefix_zero {d m k : ℕ} {W : Type*}
    [MeasurableSpace W] [StandardBorelSpace W]
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P] :
    exposedInformation (alignedExperiment (r:=k) (prefixLaw P 0 (Nat.zero_le m))) = freshInformation P.fst k := by
  have he := probability_prod_subsingleton (prefixLaw P 0 (Nat.zero_le m)) (gaussianRows 0 d)
  rw [prefixLaw_fst] at he
  simp only [he,alignedExperiment_fresh]
  change freshInformation P.fst (0+k) = freshInformation P.fst k
  rw [Nat.zero_add]




def endingRowLaw {d m : ℕ} {U V : Type*} [MeasurableSpace U] [MeasurableSpace V]
    (P : Measure (Sphere d×U))
    (κ : Kernel (U×(Rows m d×(Fin m→ℝ))) V) : Measure ((Sphere d×V)×Rows m d) :=
  (blockLaw P κ).map (fun z => ((z.1.1.1,z.2),z.1.2))

lemma measurable_endingRowMap {d m : ℕ} {U V : Type*} [MeasurableSpace U] [MeasurableSpace V] :
    Measurable (fun z : (((Sphere d×U)×Rows m d)×V) => ((z.1.1.1,z.2),z.1.2)) :=
  (measurable_fst.fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd

instance endingRowLaw_probability {d m : ℕ} {U V : Type*} [MeasurableSpace U] [MeasurableSpace V]
    (P : Measure (Sphere d×U)) [IsProbabilityMeasure P]
    (κ : Kernel (U×(Rows m d×(Fin m→ℝ))) V) [IsMarkovKernel κ] : IsProbabilityMeasure (endingRowLaw P κ) := by
  exact (Measure.isProbabilityMeasure_map_iff
    measurable_endingRowMap.aemeasurable).mpr inferInstance

lemma endingRowLaw_fst {d m : ℕ} {U V : Type*} [MeasurableSpace U] [MeasurableSpace V]
    (P : Measure (Sphere d×U))
    (κ : Kernel (U×(Rows m d×(Fin m→ℝ))) V) :
    (endingRowLaw P κ).fst = endingSignalLaw P κ := by
  rw [endingRowLaw,Measure.fst,Measure.map_map measurable_fst measurable_endingRowMap]
  rfl

lemma endingRowLaw_independence {d m : ℕ} {U V : Type*} [MeasurableSpace U] [MeasurableSpace V]
    (P : Measure (Sphere d×U)) [IsProbabilityMeasure P]
    (κ : Kernel (U×(Rows m d×(Fin m→ℝ))) V) [IsMarkovKernel κ] :
    ((endingRowLaw P κ).map swapLast).fst = P.fst.prod (gaussianRows m d) := by
  rw [endingRowLaw,Measure.fst,Measure.map_map measurable_fst swapLast.measurable,
    Measure.map_map (measurable_fst.comp swapLast.measurable) measurable_endingRowMap]
  change (blockLaw P κ).map ((Prod.map Prod.fst id) ∘ Prod.fst) = _
  rw [←Measure.map_map (measurable_fst.prodMap measurable_id) measurable_fst,←Measure.fst]
  change (((P.prod (gaussianRows m d)) ⊗ₘ κ.comap blockInput measurable_blockInput).fst).map _ = _
  rw [Measure.fst_compProd,←Measure.map_prod_map _ _ measurable_fst measurable_id,Measure.map_id]
  rfl

def blockObservedInput {d m r : ℕ} {U : Type*}
    (z : (Rows (m+r) d×(Fin (m+r)→ℝ))×U) : U×(Rows m d×(Fin m→ℝ)) :=
  (z.2, (fun j => z.1.1 (Fin.castAdd r j)), (fun j => z.1.2 (Fin.castAdd r j)))

lemma measurable_blockObservedInput {d m r : ℕ} {U : Type*} [MeasurableSpace U] :
    Measurable (blockObservedInput (d:=d) (m:=m) (r:=r) (U:=U)) := by
  unfold blockObservedInput
  fun_prop

def blockExposedBaseMap {d m r : ℕ} {U : Type*}
    (z : ((Sphere d×U)×Rows m d)×Rows r d) :
    (Rows (m+r) d×(Fin (m+r)→ℝ))×(Sphere d×U) :=
  exposedJointMap (z.1.1,Fin.append z.1.2 z.2)

lemma measurable_blockExposedBaseMap {d m r : ℕ} {U : Type*} [MeasurableSpace U] :
    Measurable (blockExposedBaseMap (d:=d) (m:=m) (r:=r) (U:=U)) :=
  measurable_exposedJointMap.comp measurable_alignedMap

lemma blockObservedInput_exposed {d m r : ℕ} {U : Type*}
    (z : ((Sphere d×U)×Rows m d)×Rows r d) :
    blockObservedInput ((blockExposedBaseMap z).1,(blockExposedBaseMap z).2.2) = blockInput z.1 := by
  unfold blockObservedInput blockExposedBaseMap exposedJointMap blockInput
  congr 2
  · funext j; simp
  · funext j; simp [label]

lemma block_exposed_processed {d m r : ℕ} {U V : Type*} [MeasurableSpace U] [MeasurableSpace V]
    (P : Measure (Sphere d×U)) [IsProbabilityMeasure P]
    (κ : Kernel (U×(Rows m d×(Fin m→ℝ))) V) [IsMarkovKernel κ] :
    processedLaw ((P.prod (gaussianRows (m+r) d)).map exposedJointMap)
      (κ.comap (blockObservedInput (r:=r)) measurable_blockObservedInput) =
      (alignedExperiment (r:=r) (endingRowLaw P κ)).map exposedJointMap := by
  let μ := P.prod (gaussianRows m d)
  let γ := gaussianRows r d
  let K := κ.comap blockInput measurable_blockInput
  let H := blockExposedBaseMap (d:=d) (m:=m) (r:=r) (U:=U)
  have hH : Measurable H := measurable_blockExposedBaseMap
  have hInput : (μ.prod γ).map H = (P.prod (gaussianRows (m+r) d)).map exposedJointMap := by
    rw [←alignedExperiment_fresh (r:=r) (m:=m) P,alignedExperiment,
      Measure.map_map measurable_exposedJointMap measurable_alignedMap]
    rfl
  have hK : ((κ.comap (blockObservedInput (r:=r)) measurable_blockObservedInput).comap
      (Prod.map id Prod.snd) (measurable_id.prodMap measurable_snd)).comap H hH =
      K.comap Prod.fst measurable_fst := by
    ext z t ht
    change κ (blockObservedInput ((H z).1,(H z).2.2)) t = κ (blockInput z.1) t
    rw [show blockObservedInput ((H z).1,(H z).2.2) = blockInput z.1 from blockObservedInput_exposed z]
  rw [processedLaw,←hInput,compProd_map_base _ _ H hH,hK,
    Measure.map_map (measurable_fst.fst.prodMk (measurable_fst.snd.fst.prodMk measurable_snd))
      (hH.prodMap measurable_id),←compProd_independent_swap μ K γ,
    Measure.map_map ((measurable_fst.fst.prodMk (measurable_fst.snd.fst.prodMk measurable_snd)).comp
      (hH.prodMap measurable_id)) ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd)]
  rw [alignedExperiment,Measure.map_map measurable_exposedJointMap measurable_alignedMap,actualExperiment,endingRowLaw]
  have he : ((blockLaw P κ).map (fun z => ((z.1.1.1,z.2),z.1.2))).prod (gaussianRows r d) =
      ((blockLaw P κ).prod (gaussianRows r d)).map (Prod.map (fun z => ((z.1.1.1,z.2),z.1.2)) id) := by
    rw [←Measure.map_prod_map _ _ measurable_endingRowMap measurable_id,Measure.map_id]
  rw [he,Measure.map_map (measurable_exposedJointMap.comp measurable_alignedMap)
    (measurable_endingRowMap.prodMap measurable_id)]
  rfl

lemma block_exposed_le_fresh {d m r : ℕ} {U V : Type*}
    [MeasurableSpace U] [MeasurableSpace V] [StandardBorelSpace U] [StandardBorelSpace V]
    [Nonempty U] [Nonempty V] [Nonempty (Sphere d)]
    (P : Measure (Sphere d×U)) [IsProbabilityMeasure P]
    (κ : Kernel (U×(Rows m d×(Fin m→ℝ))) V) [IsMarkovKernel κ] :
    exposedInformation (alignedExperiment (r:=r) (endingRowLaw P κ)) ≤ freshInformation P (m+r) := by
  let : IsProbabilityMeasure ((P.prod (gaussianRows (m+r) d)).map exposedJointMap) :=
    inferInstance
  have h := conditionalMutualInformation_processed_le ((P.prod (gaussianRows (m+r) d)).map exposedJointMap)
    (κ.comap (blockObservedInput (r:=r)) measurable_blockObservedInput)
  simpa only [block_exposed_processed,exposedInformation,freshInformation] using h



end CurrentProjection

end

end OAI
