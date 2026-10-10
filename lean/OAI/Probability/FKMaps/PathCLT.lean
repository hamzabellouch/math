import OAI.Probability.FKMaps.WalkBounds

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

local instance : MeasurableSpace C(unitInterval, ℝ) := borel _
local instance : BorelSpace C(unitInterval, ℝ) := ⟨rfl⟩

lemma pathApprox_random_tendstoInMeasure {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Ω → C(unitInterval, ℝ))
    (hX : AEMeasurable X μ) :
    TendstoInMeasure μ (fun N ω => pathApprox N (X ω)) atTop X := by
  let : MeasurableSpace C(unitInterval, ℝ) := borel _
  let : BorelSpace C(unitInterval, ℝ) := ⟨rfl⟩
  apply tendstoInMeasure_of_tendsto_ae
  · intro N
    exact ((continuous_pathApprox N).measurable.comp_aemeasurable hX).aestronglyMeasurable
  · exact ae_of_all μ (fun ω => pathApprox_tendsto (X ω))

lemma hat_gridPoint {N : ℕ} (hN : 0 < N) (i j : Fin (N+1)) :
    hat N j.val (gridPoint N i) = if i = j then 1 else 0 := by
  have hNR : (N:ℝ) ≠ 0 := by positivity
  change max 0 (1-|(N:ℝ)*((i.val:ℝ)/(N:ℝ))-(j.val:ℝ)|) = _
  rw [mul_div_cancel₀ _ hNR]
  split_ifs with hij
  · subst j
    simp
  · have hn : i.val ≠ j.val := fun h => hij (Fin.ext h)
    have hab : 1 ≤ |(i.val:ℝ)-(j.val:ℝ)| := by
      rcases lt_or_gt_of_ne hn with h | h
      · rw [abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast Nat.le_of_lt h))]
        have hh : (i.val:ℝ)+1 ≤ j.val := by exact_mod_cast h
        linarith
      · rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast Nat.le_of_lt h))]
        have hh : (j.val:ℝ)+1 ≤ i.val := by exact_mod_cast h
        linarith
    exact max_eq_left (by linarith)

lemma interpolation_gridPoint {N : ℕ} (hN : 0 < N) (a : Fin (N+1) → ℝ)
    (i : Fin (N+1)) : interpolation N a (gridPoint N i) = a i := by
  classical
  simp only [interpolation_apply,hat_gridPoint hN]
  simp

def coarseWalk {Ω : Type*} (X : ℕ → Ω → ℝ) (m n : ℕ) (ω : Ω) : C(unitInterval, ℝ) :=
  interpolation m (fun i => (∑ j ∈ Finset.range (i.val*(n/m)), X j ω)/Real.sqrt n)

def coarseIndex (m n : ℕ) (i : Fin (m+1)) : Fin (n+1) :=
  ⟨i.val*(n/m), lt_of_le_of_lt (le_trans
    (Nat.mul_le_mul_right (n/m) (Nat.le_of_lt_succ i.isLt)) (Nat.mul_div_le n m)) (Nat.lt_succ_self n)⟩

lemma coarseWalk_vertex {Ω : Type*} (X : ℕ → Ω → ℝ) (m : ℕ) {n : ℕ} (hn : 0 < n)
    (ω : Ω) (i : Fin (m+1)) :
    (∑ j ∈ Finset.range (i.val*(n/m)), X j ω)/Real.sqrt n =
      scaledWalk X n ω (gridPoint n (coarseIndex m n i)) := by
  symm
  exact interpolation_gridPoint hn _ _

lemma coarse_grid_dist_le {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (i : Fin (m+1)) :
    dist (gridPoint n (coarseIndex m n i)) (gridPoint m i) ≤ (m:ℝ)/(n:ℝ) := by
  have hmR : (0:ℝ) < m := Nat.cast_pos.mpr hm
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hi : (i.val:ℝ) ≤ m := by exact_mod_cast Nat.le_of_lt_succ i.isLt
  have hil : (i.val:ℝ) ≥ 0 := Nat.cast_nonneg _
  have hr : ((n%m:ℕ):ℝ) ≤ m := by exact_mod_cast (Nat.mod_lt n hm).le
  have hr0 : (0:ℝ) ≤ (n%m:ℕ) := Nat.cast_nonneg _
  have he : (m:ℝ)*((n/m:ℕ):ℝ)+((n%m:ℕ):ℝ) = n := by exact_mod_cast Nat.div_add_mod n m
  change |((i.val*(n/m):ℕ):ℝ)/(n:ℝ)-(i.val:ℝ)/(m:ℝ)| ≤ (m:ℝ)/(n:ℝ)
  rw [Nat.cast_mul,div_sub_div _ _ hnR.ne' hmR.ne',abs_div,abs_of_pos (mul_pos hnR hmR)]
  have hneg : (i.val:ℝ)*((n/m:ℕ):ℝ)*(m:ℝ)-(n:ℝ)*(i.val:ℝ) ≤ 0 := by nlinarith
  rw [abs_of_nonpos hneg, div_le_div_iff₀ (mul_pos hnR hmR) hnR]
  have hp := mul_le_mul hi hr hr0 (Nat.cast_nonneg m)
  have hpN := mul_le_mul_of_nonneg_right hp hnR.le
  have hei := congrArg (fun z : ℝ => (i.val:ℝ)*z*(n:ℝ)) he
  nlinarith

lemma coarseWalk_error_le {Ω : Type*} (X : ℕ → Ω → ℝ) {m n : ℕ}
    (hm : 0 < m) (hn : m*m ≤ n) (ω : Ω) {ε : ℝ} (hε : 0 ≤ ε)
    (hmod : ∀ s t : unitInterval, dist s t ≤ 2/(m:ℝ) →
      |scaledWalk X n ω s-scaledWalk X n ω t| ≤ ε) :
    ‖coarseWalk X m n ω-scaledWalk X n ω‖ ≤ ε := by
  have hn0 : 0 < n := lt_of_lt_of_le (Nat.mul_pos hm hm) hn
  have hmR : (0:ℝ) < m := Nat.cast_pos.mpr hm
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr hn0
  have hmn : (m:ℝ)/(n:ℝ) ≤ 1/(m:ℝ) := by
    rw [div_le_div_iff₀ hnR hmR,one_mul]
    exact_mod_cast hn
  apply (ContinuousMap.norm_le _ hε).mpr
  intro t
  change |interpolation m _ t-scaledWalk X n ω t| ≤ ε
  apply interpolation_sub_const_bound
  intro i hi
  rw [coarseWalk_vertex X m hn0 ω i]
  apply hmod
  calc dist (gridPoint n (coarseIndex m n i)) t
      ≤ dist (gridPoint n (coarseIndex m n i)) (gridPoint m i)+dist (gridPoint m i) t := dist_triangle _ _ _
    _ ≤ (m:ℝ)/(n:ℝ)+1/(m:ℝ) := add_le_add (coarse_grid_dist_le hm hn0 i) (hat_gridPoint_dist hm i t hi).le
    _ ≤ 2/(m:ℝ) := by
      calc (m:ℝ)/(n:ℝ)+1/(m:ℝ) ≤ 1/(m:ℝ)+1/(m:ℝ) := add_le_add hmn le_rfl
        _ = 2/(m:ℝ) := by ring

def cumulative (m : ℕ) (a : Fin m → ℝ) (i : Fin (m+1)) : ℝ :=
  ∑ j ∈ Finset.range i.val, if h : j < m then a ⟨j,h⟩ else 0

lemma continuous_cumulative (m : ℕ) : Continuous (cumulative m) := by
  apply continuous_pi
  intro i
  unfold cumulative
  apply continuous_finsetSum
  intro j _
  split_ifs <;> fun_prop

lemma cumulative_nat (m : ℕ) (a : ℕ → ℝ) (i : Fin (m+1)) :
    cumulative m (fun j => a j.val) i = ∑ j ∈ Finset.range i.val, a j := by
  unfold cumulative
  apply Finset.sum_congr rfl
  intro j hj
  exact dite_eq_left (lt_of_lt_of_le (Finset.mem_range.mp hj) (Nat.le_of_lt_succ i.isLt))

lemma cumulative_div (m : ℕ) (a : Fin m → ℝ) (c : ℝ) (i : Fin (m+1)) :
    cumulative m (fun j => a j/c) i = cumulative m a i/c := by
  simp only [cumulative, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp

lemma sum_range_blocks (f : ℕ → ℝ) (k l : ℕ) :
    (∑ i ∈ Finset.range k, ∑ j ∈ Finset.range l, f (i*l+j)) =
      ∑ j ∈ Finset.range (k*l), f j := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ,ih,Nat.succ_mul,Finset.sum_range_add]

lemma cumulative_blocks (m l : ℕ) (f : ℕ → ℝ) (i : Fin (m+1)) :
    cumulative m (fun k => ∑ j : Fin l, f (k.val*l+j.val)) i =
      ∑ j ∈ Finset.range (i.val*l), f j := by
  rw [cumulative_nat m (fun k => ∑ j : Fin l, f (k*l+j.val)) i]
  have hf (k : ℕ) : (∑ j : Fin l, f (k*l+j.val)) = ∑ j ∈ Finset.range l, f (k*l+j) :=
    Fin.sum_univ_eq_sum_range (fun j => f (k*l+j)) l
  simp_rw [hf]
  exact sum_range_blocks f i.val l

lemma coarseWalk_eq_cumulative {Ω : Type*} (X : ℕ → Ω → ℝ) (m n : ℕ) (ω : Ω) :
    interpolation m (cumulative m (fun i => (∑ j : Fin (n/m), X (i.val*(n/m)+j.val) ω)/Real.sqrt n)) =
      coarseWalk X m n ω := by
  unfold coarseWalk
  congr 1
  funext i
  rw [cumulative_div,cumulative_blocks m (n/m) (fun j => X j ω) i]

lemma map_uncurry_pi {ι κ : Type*} [Fintype ι] [Fintype κ]
    (μ : ι → κ → Measure ℝ) [∀ i j, IsProbabilityMeasure (μ i j)] :
    (Measure.pi (fun i => Measure.pi (μ i))).map (fun x (ij : ι×κ) => x ij.1 ij.2) =
      Measure.pi (fun ij : ι×κ => μ ij.1 ij.2) := by
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply (Measurable.of_eval (fun ij =>
    (measurable_pi_apply ij.2).comp (measurable_pi_apply ij.1))) (.univ_pi hs)]
  have heq : (fun x (ij : ι×κ) => x ij.1 ij.2) ⁻¹' univ.pi s =
      univ.pi (fun i => univ.pi (fun j => s (i,j))) := by
    ext x
    simp
  rw [heq,Measure.pi_pi]
  simp only [Measure.pi_pi]
  exact (Fintype.prod_prod_type (fun ij : ι×κ => μ ij.1 ij.2 (s ij))).symm

lemma iIndepFun_uncurry_pi {ι κ Ω : Type*} [Fintype ι] [Fintype κ]
    [MeasurableSpace Ω] (μ : ι → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (X : ι → κ → Ω → ℝ) (hm : ∀ i j, AEMeasurable (X i j) (μ i))
    (hX : ∀ i, iIndepFun (X i) (μ i)) :
    iIndepFun (fun ij : ι×κ => fun ω : ι → Ω => X ij.1 ij.2 (ω ij.1)) (Measure.pi μ) := by
  have hrow (i) : AEMeasurable (fun ω j => X i j ω) (μ i) :=
    AEMeasurable.of_eval (hm i)
  have hmap : (Measure.pi μ).map (fun ω i j => X i j (ω i)) =
      Measure.pi (fun i => Measure.pi (fun j => (μ i).map (X i j))) := by
    rw [Measure.pi_map_pi (fun i => hrow i)]
    congr 1
    funext i
    exact iIndepFun.map_fun_eq_pi_map (hm i) (hX i)
  have hmflat : ∀ ij : ι×κ, AEMeasurable
      (fun ω : ι → Ω => X ij.1 ij.2 (ω ij.1)) (Measure.pi μ) := fun ij =>
    (hm _ _).comp_quasiMeasurePreserving (measurePreserving_eval μ ij.1).quasiMeasurePreserving
  rw [iIndepFun_iff_map_fun_eq_pi_map hmflat]
  have heq : (fun (ω : ι → Ω) (ij : ι×κ) => X ij.1 ij.2 (ω ij.1)) =
      (fun x (ij : ι×κ) => x ij.1 ij.2) ∘ (fun (ω : ι → Ω) i j => X i j (ω i)) := rfl
  have hrm : AEMeasurable (fun ω : ι → Ω => fun i j => X i j (ω i)) (Measure.pi μ) :=
    AEMeasurable.of_eval (fun i => (hrow i).comp_quasiMeasurePreserving
      (measurePreserving_eval μ i).quasiMeasurePreserving)
  have hflatm : Measurable (fun x : ι → κ → ℝ => fun ij : ι×κ => x ij.1 ij.2) := by fun_prop
  rw [heq, ← AEMeasurable.map_map_of_aemeasurable hflatm.aemeasurable hrm, hmap]
  rw [map_uncurry_pi]
  congr 1
  funext ij
  have he := measurePreserving_eval μ ij.1
  change (μ ij.1).map (X ij.1 ij.2) = (Measure.pi μ).map ((X ij.1 ij.2) ∘ Function.eval ij.1)
  have ha : AEMeasurable (X ij.1 ij.2) ((Measure.pi μ).map (Function.eval ij.1)) :=
    he.map_eq.symm ▸ hm ij.1 ij.2
  rw [← AEMeasurable.map_map_of_aemeasurable ha he.measurable.aemeasurable, he.map_eq]

lemma tendstoInDistribution_pi_indep {ι α Ω Ω' : Type*} [Fintype ι]
    [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ : Measure Ω} {ν : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {l : Filter α} {X : ι → α → Ω → ℝ} {Z : ι → Ω' → ℝ}
    (h : ∀ i, TendstoInDistribution (X i) l (Z i) (fun _ => μ) ν)
    (hX : ∀ n, iIndepFun (fun i => X i n) μ) (hZ : iIndepFun Z ν) :
    TendstoInDistribution (fun n ω i => X i n ω) l (fun ω i => Z i ω) (fun _ => μ) ν := by
  have hm : ∀ n, AEMeasurable (fun ω i => X i n ω) μ :=
    fun n => AEMeasurable.of_eval (fun i => (h i).forall_aemeasurable n)
  have hz : AEMeasurable (fun ω i => Z i ω) ν :=
    AEMeasurable.of_eval (fun i => (h i).aemeasurable_limit)
  refine ⟨hm,hz,?_⟩
  have hp := ProbabilityMeasure.continuous_pi.tendsto
    (fun i => (⟨ν.map (Z i), inferInstance⟩ :
      ProbabilityMeasure ℝ))
  have ht := hp.comp (tendsto_pi_nhds.mpr (fun i => (h i).tendsto))
  have heq (n : α) : (⟨μ.map (fun ω i => X i n ω),
      inferInstance⟩ : ProbabilityMeasure (ι → ℝ)) =
      ProbabilityMeasure.pi (fun i => (⟨μ.map (X i n),
        inferInstance⟩ : ProbabilityMeasure ℝ)) := by
    apply Subtype.ext
    exact iIndepFun.map_fun_eq_pi_map (fun i => (h i).forall_aemeasurable n) (hX n)
  have hzeq : (⟨ν.map (fun ω i => Z i ω), inferInstance⟩ :
      ProbabilityMeasure (ι → ℝ)) = ProbabilityMeasure.pi (fun i => (⟨ν.map (Z i),
        inferInstance⟩ : ProbabilityMeasure ℝ)) := by
    apply Subtype.ext
    exact iIndepFun.map_fun_eq_pi_map (fun i => (h i).aemeasurable_limit) hZ
  simp_rw [heq,hzeq]
  exact ht

lemma identDistrib_pi_indep {ι Ω Ω' : Type*} [Fintype ι]
    [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ : Measure Ω} {ν : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : ι → Ω → ℝ} {Y : ι → Ω' → ℝ}
    (hX : iIndepFun X μ) (hY : iIndepFun Y ν)
    (h : ∀ i, IdentDistrib (X i) (Y i) μ ν) :
    IdentDistrib (fun ω i => X i ω) (fun ω i => Y i ω) μ ν := by
  refine ⟨AEMeasurable.of_eval (fun i => (h i).aemeasurable_fst),
    AEMeasurable.of_eval (fun i => (h i).aemeasurable_snd), ?_⟩
  rw [iIndepFun.map_fun_eq_pi_map (fun i => (h i).aemeasurable_fst) hX,
    iIndepFun.map_fun_eq_pi_map (fun i => (h i).aemeasurable_snd) hY]
  congr 1
  funext i
  exact (h i).map_eq

lemma blockIndex_injective (m l : ℕ) :
    Function.Injective (fun ij : Fin m × Fin l => ij.1.val*l+ij.2.val) := by
  rintro ⟨i,j⟩ ⟨i',j'⟩ h
  change i.val*l+j.val = i'.val*l+j'.val at h
  have hii : i.val = i'.val := by
    by_contra hh
    rcases lt_or_gt_of_ne hh with hlt | hgt
    · have hp : (i.val+1)*l ≤ i'.val*l := Nat.mul_le_mul_right l hlt
      nlinarith [j.isLt,j'.isLt]
    · have hp : (i'.val+1)*l ≤ i.val*l := Nat.mul_le_mul_right l hgt
      nlinarith [j.isLt,j'.isLt]
  have hjj : j.val = j'.val := by
    rw [hii] at h
    exact Nat.add_left_cancel h
  exact Prod.ext (Fin.ext hii) (Fin.ext hjj)

lemma identDistrib_iid_blocks {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hm : ∀ k, AEMeasurable (X k) μ) (hind : iIndepFun X μ)
    (hid : ∀ k, IdentDistrib (X k) (X 0) μ μ) (m l : ℕ) :
    IdentDistrib
      (fun ω (i : Fin m) => ∑ j : Fin l, X (i.val*l+j.val) ω)
      (fun ω : Fin m → Ω => fun i => ∑ j : Fin l, X j.val (ω i))
      μ (Measure.pi (fun _ : Fin m => μ)) := by
  have hi₁ : iIndepFun (fun ij : Fin m × Fin l => X (ij.1.val*l+ij.2.val)) μ :=
    hind.precomp (blockIndex_injective m l)
  have hi₂ : iIndepFun (fun ij : Fin m × Fin l => fun ω : Fin m → Ω => X ij.2.val (ω ij.1))
      (Measure.pi (fun _ : Fin m => μ)) :=
    iIndepFun_uncurry_pi (fun _ : Fin m => μ) (fun _ (j : Fin l) => X j.val)
      (fun _ j => hm j.val) (fun _ => hind.precomp Fin.val_injective)
  have he (ij : Fin m × Fin l) :
      IdentDistrib (X (ij.1.val*l+ij.2.val))
        (fun ω : Fin m → Ω => X ij.2.val (ω ij.1)) μ (Measure.pi (fun _ : Fin m => μ)) := by
    have heval : IdentDistrib (fun ω : Fin m → Ω => X ij.2.val (ω ij.1)) (X ij.2.val)
        (Measure.pi (fun _ : Fin m => μ)) μ := by
      have hp := measurePreserving_eval (fun _ : Fin m => μ) ij.1
      refine ⟨(hm _).comp_quasiMeasurePreserving hp.quasiMeasurePreserving,hm _,?_⟩
      change (Measure.pi (fun _ : Fin m => μ)).map ((X ij.2.val) ∘ Function.eval ij.1) = μ.map (X ij.2.val)
      have ha : AEMeasurable (X ij.2.val) ((Measure.pi (fun _ : Fin m => μ)).map (Function.eval ij.1)) :=
        hp.map_eq.symm ▸ hm _
      rw [← AEMeasurable.map_map_of_aemeasurable ha hp.measurable.aemeasurable,hp.map_eq]
    exact ((hid _).trans (hid _).symm).trans heval.symm
  have hvec := identDistrib_pi_indep hi₁ hi₂ he
  exact hvec.comp (u := fun x (i : Fin m) => ∑ j : Fin l, x (i,j)) (by fun_prop)

lemma tendstoInDistribution_transport {α E Ω₁ Ω₂ Ω₃ Ω₄ : Type*}
    [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace Ω₃] [MeasurableSpace Ω₄]
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂} {μ₃ : Measure Ω₃} {μ₄ : Measure Ω₄}
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    [IsProbabilityMeasure μ₃] [IsProbabilityMeasure μ₄]
    {X : α → Ω₁ → E} {Y : α → Ω₂ → E} {Z : Ω₃ → E} {W : Ω₄ → E}
    {l : Filter α} (h : TendstoInDistribution X l Z (fun _ => μ₁) μ₃)
    (hXY : ∀ n, IdentDistrib (X n) (Y n) μ₁ μ₂) (hZW : IdentDistrib Z W μ₃ μ₄) :
    TendstoInDistribution Y l W (fun _ => μ₂) μ₄ := by
  refine ⟨fun n => (hXY n).aemeasurable_snd,hZW.aemeasurable_snd,?_⟩
  have heq (n : α) :
      (⟨μ₂.map (Y n), inferInstance⟩ : ProbabilityMeasure E) =
      ⟨μ₁.map (X n), inferInstance⟩ :=
    Subtype.ext (hXY n).map_eq.symm
  have hz : (⟨μ₄.map W, inferInstance⟩ : ProbabilityMeasure E) =
      ⟨μ₃.map Z, inferInstance⟩ :=
    Subtype.ext hZW.map_eq.symm
  simp_rw [heq,hz]
  exact h.tendsto

lemma tendstoInDistribution_reindex {α β E Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [TopologicalSpace E]
    [MeasurableSpace E] [OpensMeasurableSpace E]
    {μ : Measure Ω} {ν : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : α → Ω → E} {Z : Ω' → E} {l : Filter α} {l' : Filter β} {f : β → α}
    (h : TendstoInDistribution X l Z (fun _ => μ) ν) (hf : Tendsto f l' l) :
    TendstoInDistribution (fun n => X (f n)) l' Z (fun _ => μ) ν :=
  ⟨fun n => h.forall_aemeasurable (f n), h.aemeasurable_limit,h.tendsto.comp hf⟩

lemma identDistrib_comp_measurePreserving {Ω Ω' E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace E]
    {μ : Measure Ω} {ν : Measure Ω'} {f : Ω' → Ω} {X : Ω → E}
    (hf : MeasurePreserving f ν μ) (hX : AEMeasurable X μ) :
    IdentDistrib (X ∘ f) X ν μ := by
  refine ⟨hX.comp_quasiMeasurePreserving hf.quasiMeasurePreserving,hX,?_⟩
  have ha : AEMeasurable X (ν.map f) := hf.map_eq.symm ▸ hX
  rw [← AEMeasurable.map_map_of_aemeasurable ha hf.measurable.aemeasurable,hf.map_eq]

lemma iid_block_standard_CLT {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {ν : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : ℕ → Ω → ℝ) (h0 : ∫ ω, X 0 ω ∂μ = 0) (h1 : ∫ ω, (X 0 ω)^2 ∂μ = 1)
    (hind : iIndepFun X μ) (hid : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    {m : ℕ} (Z : Fin m → Ω' → ℝ) (hZ : ∀ i, HasLaw (Z i) (gaussianReal 0 1) ν)
    (hindZ : iIndepFun Z ν) :
    TendstoInDistribution
      (fun (l : ℕ) ω (i : Fin m) => (Real.sqrt l)⁻¹ * ∑ j : Fin l, X (i.val*l+j.val) ω)
      atTop (fun ω i => Z i ω) (fun _ => μ) ν := by
  let S : ℕ → Ω → ℝ := fun l ω => (Real.sqrt l)⁻¹ * ∑ k ∈ Finset.range l, X k ω
  have hm (l) : AEMeasurable (S l) μ :=
    (Finset.aemeasurable_fun_sum _ (fun k _ => (hid k).aemeasurable_fst)).const_mul _
  have hv (i : Fin m) : TendstoInDistribution
      (fun l (ω : Fin m → Ω) => S l (ω i)) atTop (Z i)
      (fun _ => Measure.pi (fun _ : Fin m => μ)) ν := by
    have hc := tendstoInDistribution_inv_sqrt_mul_sum (hZ i) h0 h1 hind hid
    apply tendstoInDistribution_transport hc
      (fun l => (identDistrib_comp_measurePreserving
        (measurePreserving_eval (fun _ : Fin m => μ) i) (hm l)).symm)
      (IdentDistrib.refl (hZ i).aemeasurable)
  have hj := tendstoInDistribution_pi_indep hv
    (fun l => iIndepFun_pi (fun _ : Fin m => hm l)) hindZ
  apply tendstoInDistribution_transport hj
    (fun l => ?_) (IdentDistrib.refl (AEMeasurable.of_eval (fun i => (hZ i).aemeasurable)))
  have hblk := (identDistrib_iid_blocks X (fun k => (hid k).aemeasurable_fst) hind hid m l).symm
  have hh := hblk.comp (u := fun x (i : Fin m) => (Real.sqrt l)⁻¹ * x i) (by fun_prop)
  change IdentDistrib (fun ω : Fin m → Ω => fun i => (Real.sqrt l)⁻¹ * ∑ j : Fin l, X j.val (ω i))
    (fun ω i => (Real.sqrt l)⁻¹ * ∑ j : Fin l, X (i.val*l+j.val) ω) _ _ at hh
  have heq : (fun ω : Fin m → Ω => fun i => (Real.sqrt l)⁻¹ * ∑ j : Fin l, X j.val (ω i)) =
      (fun ω : Fin m → Ω => fun i => S l (ω i)) := by
    funext ω i
    dsimp [S]
    rw [Fin.sum_univ_eq_sum_range (fun k => X k (ω i)) l]
  rw [heq] at hh
  exact hh

lemma nat_div_ratio_tendsto {m : ℕ} (hm : 0 < m) :
    Tendsto (fun n : ℕ => ((n/m:ℕ):ℝ)/(n:ℝ)) atTop (𝓝 ((m:ℝ)⁻¹)) := by
  have ht := ((tendsto_const_nhds (x := (1:ℝ))).sub (tendsto_mod_div_atTop_nhds_zero_nat hm)).div_const (m:ℝ)
  have hlim : ((1:ℝ)-0)/(m:ℝ) = (m:ℝ)⁻¹ := by simp
  rw [hlim] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have he : (n:ℝ) = (m:ℝ)*((n/m:ℕ):ℝ)+((n%m:ℕ):ℝ) := by
    exact_mod_cast (Nat.div_add_mod n m).symm
  have hm0 : (m:ℝ) ≠ 0 := by positivity
  have hn0 : (n:ℝ) ≠ 0 := by positivity
  field_simp
  nlinarith

lemma sqrt_nat_div_ratio_tendsto {m : ℕ} (hm : 0 < m) :
    Tendsto (fun n : ℕ => Real.sqrt ((n/m:ℕ):ℝ) / Real.sqrt n) atTop (𝓝 ((Real.sqrt m)⁻¹)) := by
  have ht := (nat_div_ratio_tendsto hm).sqrt
  simpa only [Real.sqrt_div (Nat.cast_nonneg _), Real.sqrt_inv] using ht

lemma iid_block_scaled_CLT {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {ν : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : ℕ → Ω → ℝ) (h0 : ∫ ω, X 0 ω ∂μ = 0) (h1 : ∫ ω, (X 0 ω)^2 ∂μ = 1)
    (hind : iIndepFun X μ) (hid : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    {m : ℕ} (hm : 0 < m) (Z : Fin m → Ω' → ℝ)
    (hZ : ∀ i, HasLaw (Z i) (gaussianReal 0 1) ν) (hindZ : iIndepFun Z ν) :
    TendstoInDistribution
      (fun (n : ℕ) ω (i : Fin m) => (∑ j : Fin (n/m), X (i.val*(n/m)+j.val) ω)/Real.sqrt n)
      atTop (fun ω i => (Real.sqrt m)⁻¹ * Z i ω) (fun _ => μ) ν := by
  have hc := tendstoInDistribution_reindex (iid_block_standard_CLT X h0 h1 hind hid Z hZ hindZ)
    (Nat.tendsto_div_const_atTop hm.ne')
  have hr : TendstoInMeasure μ (fun n (_ : Ω) => Real.sqrt ((n/m:ℕ):ℝ)/Real.sqrt n) atTop
      (fun _ => (Real.sqrt m)⁻¹) := by
    exact tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
      (ae_of_all μ (fun _ => sqrt_nat_div_ratio_tendsto hm))
  have hmul := hc.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun x : (Fin m → ℝ) × ℝ => fun i => x.2*x.1 i) (by fun_prop) hr
    (fun _ => aemeasurable_const)
  apply hmul.congr (fun n => ae_of_all μ (fun ω => ?_)) (ae_of_all ν (fun _ => rfl))
  funext i
  change (Real.sqrt ((n/m:ℕ):ℝ)/Real.sqrt n) *
    ((Real.sqrt ((n/m:ℕ):ℝ))⁻¹ * ∑ j : Fin (n/m), X (i.val*(n/m)+j.val) ω) = _
  have hsum : (∑ j : Fin (n/m), X (i.val*(n/m)+j.val) ω) =
      ∑ j ∈ Finset.range (n/m), X (i.val*(n/m)+j) ω :=
    Fin.sum_univ_eq_sum_range (fun j => X (i.val*(n/m)+j) ω) (n/m)
  rw [hsum]
  by_cases hl : n/m = 0
  · simp [hl]
  · have hlt : (0:ℝ) < (n/m:ℕ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hl)
    have hsn : Real.sqrt ((n/m:ℕ):ℝ) ≠ 0 := (Real.sqrt_pos.mpr hlt).ne'
    field_simp

local instance : MeasurableSpace C(unitInterval, ℝ) := borel _
local instance : BorelSpace C(unitInterval, ℝ) := ⟨rfl⟩

def gridTime (m : ℕ) (i : Fin (m+1)) : ℝ≥0 := ⟨(i.val:ℝ)/(m:ℝ), by positivity⟩

lemma gridTime_mono (m : ℕ) : Monotone (gridTime m) := by
  intro i j hij
  change (i.val:ℝ)/(m:ℝ) ≤ (j.val:ℝ)/(m:ℝ)
  exact div_le_div_of_nonneg_right (Nat.cast_le.mpr hij) (Nat.cast_nonneg m)

def meshIncrement {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (m : ℕ) (i : Fin m) (ω : Ω) : ℝ :=
  B (gridTime m i.succ) ω-B (gridTime m i.castSucc) ω

lemma brownian_mesh_independent {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (m : ℕ) :
    iIndepFun (meshIncrement B m) μ :=
  hB.hasIndepIncrements m (gridTime m) (gridTime_mono m)

lemma brownian_mesh_hasLaw {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) {m : ℕ} (i : Fin m) :
    HasLaw (meshIncrement B m i) (gaussianReal 0 ((m:ℝ≥0)⁻¹)) μ := by
  have h := hB.hasLaw_sub (gridTime m i.succ) (gridTime m i.castSucc)
  have hd : nndist (gridTime m i.succ).val (gridTime m i.castSucc).val = (m:ℝ≥0)⁻¹ := by
    apply NNReal.coe_injective
    change |((i.val+1:ℕ):ℝ)/(m:ℝ)-(i.val:ℝ)/(m:ℝ)| = (m:ℝ)⁻¹
    rw [← sub_div, Nat.cast_add, Nat.cast_one]
    simp only [add_sub_cancel_left, one_div, abs_inv, abs_of_nonneg (show (0:ℝ) ≤ m from Nat.cast_nonneg m)]
  change HasLaw (B (gridTime m i.succ) - B (gridTime m i.castSucc)) _ _
  simpa only [hd] using h

lemma brownian_normalized_mesh_hasLaw {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) {m : ℕ} (hm : 0 < m) (i : Fin m) :
    HasLaw (fun ω => Real.sqrt m * meshIncrement B m i ω) (gaussianReal 0 1) μ := by
  have h := gaussianReal_const_mul (brownian_mesh_hasLaw hB i) (Real.sqrt m)
  convert h using 1
  congr 1
  · simp
  · apply NNReal.coe_injective
    simp [Real.sq_sqrt, Nat.cast_nonneg, ne_of_gt hm]

def brownianPath {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (ω : Ω) : C(unitInterval, ℝ) :=
  ContinuousMap.mkD (fun t => B ⟨(t:ℝ),t.property.1⟩ ω) 0

lemma brownianPath_ae_eq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ) :
    ∀ᵐ ω ∂μ, ∀ t : unitInterval, brownianPath B ω t = B ⟨(t:ℝ),t.property.1⟩ ω := by
  filter_upwards [hB.cont] with ω hω
  intro t
  exact ContinuousMap.mkD_apply_of_continuous (hω.comp (by fun_prop))

lemma brownianPath_aemeasurable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ) :
    AEMeasurable (brownianPath B) μ := by
  have hem : MeasurableEmbedding (fun f : C(unitInterval, ℝ) =>
      fun n : ℕ => f (TopologicalSpace.denseSeq unitInterval n)) := by
    apply Continuous.measurableEmbedding
    · apply continuous_pi
      intro n
      fun_prop
    · intro f g hfg
      apply ContinuousMap.ext
      exact congrFun ((TopologicalSpace.denseRange_denseSeq unitInterval).equalizer
        f.continuous g.continuous hfg)
  apply hem.aemeasurable_comp_iff.mp
  apply AEMeasurable.of_eval
  intro n
  apply (hB.aemeasurable _).congr
  filter_upwards [brownianPath_ae_eq hB] with ω hω
  exact (hω _).symm

lemma cumulative_mesh {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (m : ℕ) (ω : Ω) (i : Fin (m+1)) :
    cumulative m (fun j => meshIncrement B m j ω) i = B (gridTime m i) ω-B 0 ω := by
  let g : ℕ → ℝ := fun k => B ⟨(k:ℝ)/(m:ℝ), by positivity⟩ ω
  have he0 : g 0 = B 0 ω := by
    simp only [g,Nat.cast_zero,zero_div]
    rfl
  rw [← he0]
  change cumulative m (fun j => g (j.val+1)-g j.val) i = g i.val-g 0
  rw [cumulative_nat m (fun j => g (j+1)-g j) i,Finset.sum_range_sub]

lemma coarseWalk_CLT {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {ν : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : ℕ → Ω → ℝ) (h0 : ∫ ω, X 0 ω ∂μ = 0) (h1 : ∫ ω, (X 0 ω)^2 ∂μ = 1)
    (hind : iIndepFun X μ) (hid : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    {B : ℝ≥0 → Ω' → ℝ} (hB : IsBrownianReal B ν) {m : ℕ} (hm : 0 < m) :
    TendstoInDistribution (coarseWalk X m) atTop (fun ω => pathApprox m (brownianPath B ω))
      (fun _ => μ) ν := by
  have hc := iid_block_scaled_CLT X h0 h1 hind hid hm
    (fun i ω => Real.sqrt m*meshIncrement B m i ω)
    (brownian_normalized_mesh_hasLaw hB.toIsPreBrownianReal hm)
    ((brownian_mesh_independent hB.toIsPreBrownianReal m).comp
      (fun _ x => Real.sqrt m*x) (by fun_prop))
  have hs : Real.sqrt (m:ℝ) ≠ 0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hm)).ne'
  have hcm : TendstoInDistribution
      (fun (n : ℕ) ω (i : Fin m) => (∑ j : Fin (n/m), X (i.val*(n/m)+j.val) ω)/Real.sqrt n)
      atTop (fun ω i => meshIncrement B m i ω) (fun _ => μ) ν :=
    hc.congr (fun _ => ae_of_all μ (fun _ => rfl)) (ae_of_all ν (fun ω => by
      funext i
      exact inv_mul_cancel_left₀ hs _))
  have hp := hcm.continuous_comp ((continuous_interpolation m).comp (continuous_cumulative m))
  apply hp.congr (fun n => ae_of_all μ (fun ω => coarseWalk_eq_cumulative X m n ω))
  filter_upwards [brownianPath_ae_eq hB,hB.eval_zero_ae_eq_zero] with ω hω hzero
  change interpolation m _ = interpolation m _
  congr 1
  funext i
  rw [cumulative_mesh,hzero,sub_zero]
  exact (hω (gridPoint m i)).symm

lemma integral_lipschitz_approx_bound {E Ω : Type*} [PseudoMetricSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X Y : Ω → E} (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    {F : E → ℝ} {M : ℝ} (hM : ∀ x y, dist (F x) (F y) ≤ M)
    {L : ℝ≥0} (hL : LipschitzWith L F) {δ : ℝ} (hδ : 0 ≤ δ) :
    |(∫ ω, F (X ω) ∂μ) - ∫ ω, F (Y ω) ∂μ| ≤
      L*δ + M*μ.real {ω | δ ≤ dist (X ω) (Y ω)} := by
  have hne : Nonempty Ω := nonempty_of_isProbabilityMeasure μ
  let x₀ := X (Classical.choice hne)
  have h_int (Z : Ω → E) (hZ : AEMeasurable Z μ) : Integrable (fun ω => F (Z ω)) μ := by
    refine Integrable.of_bound ((hL.continuous.measurable.comp_aemeasurable hZ).aestronglyMeasurable)
      (‖F x₀‖+M) (ae_of_all μ (fun ω => ?_))
    have h := hM (Z ω) x₀
    rw [Real.dist_eq] at h
    simpa only [Real.norm_eq_abs] using
      (show |F (Z ω)| ≤ |F x₀|+M from by linarith [abs_sub_abs_le_abs_sub (F (Z ω)) (F x₀)])
  have hi : Integrable (fun ω => F (X ω)-F (Y ω)) μ :=
    (h_int X hX).sub (h_int Y hY)
  have his := hi.norm
  have hset : NullMeasurableSet {ω | dist (X ω) (Y ω) < δ} μ :=
    nullMeasurableSet_lt (hX.dist hY) aemeasurable_const
  rw [← integral_sub (h_int X hX) (h_int Y hY), ← Real.norm_eq_abs]
  calc
    ‖∫ ω, F (X ω)-F (Y ω) ∂μ‖ ≤ ∫ ω, ‖F (X ω)-F (Y ω)‖ ∂μ :=
      norm_integral_le_integral_norm _
    _ = (∫ ω in {ω | dist (X ω) (Y ω) < δ}, ‖F (X ω)-F (Y ω)‖ ∂μ) +
        ∫ ω in {ω | δ ≤ dist (X ω) (Y ω)}, ‖F (X ω)-F (Y ω)‖ ∂μ := by
      symm
      simpa only [Set.compl_ofPred, not_lt] using integral_add_compl₀ hset his
    _ ≤ (∫ _ in {ω | dist (X ω) (Y ω) < δ}, (L : ℝ)*δ ∂μ) +
        ∫ _ in {ω | δ ≤ dist (X ω) (Y ω)}, M ∂μ := by
      apply add_le_add
      · apply setIntegral_mono_on₀ his.integrableOn integrableOn_const hset
        intro ω hω
        rw [← dist_eq_norm]
        exact (hL.dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left hω.le L.coe_nonneg)
      · apply setIntegral_mono his.integrableOn integrableOn_const
        intro ω
        exact hM _ _
    _ = (L:ℝ)*δ*μ.real {ω | dist (X ω) (Y ω) < δ} +
        M*μ.real {ω | δ ≤ dist (X ω) (Y ω)} := by
      simp only [integral_const, measureReal_restrict_apply, MeasurableSet.univ,
        Set.univ_inter, smul_eq_mul]
      ring
    _ ≤ _ := by
      exact add_le_add (by
        calc (L:ℝ)*δ*μ.real {ω | dist (X ω) (Y ω) < δ}
            ≤ (L:ℝ)*δ*1 := mul_le_mul_of_nonneg_left measureReal_le_one (mul_nonneg L.coe_nonneg hδ)
          _ = (L:ℝ)*δ := mul_one _) le_rfl

theorem tendstoInDistribution_of_approximations {E Ω Ω' : Type*}
    [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ : Measure Ω} {ν : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : ℕ → Ω → E} {Y : Ω' → E} {A : ℕ → ℕ → Ω → E} {B : ℕ → Ω' → E}
    (hX : ∀ n, AEMeasurable (X n) μ) (hY : AEMeasurable Y ν)
    (hAB : ∀ m, TendstoInDistribution (A m) atTop (B m) (fun _ => μ) ν)
    (ha : ∀ δ > 0, ∀ η > 0, ∃ m,
      (∀ᶠ n in atTop, μ.real {ω | δ ≤ dist (X n ω) (A m n ω)} ≤ η) ∧
      ν.real {ω | δ ≤ dist (Y ω) (B m ω)} ≤ η) :
    TendstoInDistribution X atTop Y (fun _ => μ) ν := by
  refine ⟨hX,hY,?_⟩
  apply tendsto_iff_forall_lipschitz_integral_tendsto.mpr
  rintro F ⟨M,hM⟩ ⟨L,hL⟩
  have hne : Nonempty Ω' := nonempty_of_isProbabilityMeasure ν
  have hM0 : 0 ≤ M := by simpa using hM (Y (Classical.choice hne)) (Y (Classical.choice hne))
  change Tendsto (fun n => ∫ ω, F ω ∂(μ.map (X n))) atTop (𝓝 (∫ ω, F ω ∂(ν.map Y)))
  simp_rw [integral_map (hX _) hL.continuous.aestronglyMeasurable,
    integral_map hY hL.continuous.aestronglyMeasurable]
  rw [Metric.tendsto_nhds]
  intro ε hε
  let δ := ε/(8*((L:ℝ)+1))
  let η := ε/(8*(M+1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hη : 0 < η := by dsimp [η]; positivity
  have hLd : (L:ℝ)*δ ≤ ε/8 := by
    dsimp [δ]
    rw [← mul_div_assoc, div_le_iff₀ (by positivity : 0 < 8*((L:ℝ)+1))]
    nlinarith [L.coe_nonneg]
  have hMe : M*η ≤ ε/8 := by
    dsimp [η]
    rw [← mul_div_assoc, div_le_iff₀ (by positivity : 0 < 8*(M+1))]
    nlinarith
  obtain ⟨m,hm,hb⟩ := ha δ hδ η hη
  have hmid := (tendsto_iff_forall_lipschitz_integral_tendsto.mp (hAB m).tendsto)
    F ⟨M,hM⟩ ⟨L,hL⟩
  change Tendsto (fun n => ∫ ω, F ω ∂(μ.map (A m n))) atTop
    (𝓝 (∫ ω, F ω ∂(ν.map (B m)))) at hmid
  simp_rw [integral_map ((hAB m).forall_aemeasurable _) hL.continuous.aestronglyMeasurable,
    integral_map (hAB m).aemeasurable_limit hL.continuous.aestronglyMeasurable] at hmid
  have hme := (Metric.tendsto_nhds.mp hmid) (ε/4) (by positivity)
  filter_upwards [hm,hme] with n hn hnmid
  have hbnd₁ := integral_lipschitz_approx_bound (hX n) ((hAB m).forall_aemeasurable n) hM hL hδ.le
  have hbnd₂ := integral_lipschitz_approx_bound hY (hAB m).aemeasurable_limit hM hL hδ.le
  have hsum := abs_sub_le (∫ ω, F (X n ω) ∂μ) (∫ ω, F (A m n ω) ∂μ) (∫ ω, F (Y ω) ∂ν)
  have hsum₂ := abs_sub_le (∫ ω, F (A m n ω) ∂μ) (∫ ω, F (B m ω) ∂ν) (∫ ω, F (Y ω) ∂ν)
  rw [abs_sub_comm (∫ ω, F (B m ω) ∂ν) (∫ ω, F (Y ω) ∂ν)] at hsum₂
  rw [Real.dist_eq] at hnmid ⊢
  have hpe₁ := mul_le_mul_of_nonneg_left hn hM0
  have hpe₂ := mul_le_mul_of_nonneg_left hb hM0
  linarith

theorem iid_scaledWalk_CLT {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {ν : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : ℕ → Ω → ℝ) (hXm : ∀ k, Measurable (X k)) (hX₂ : MemLp (X 0) 2 μ)
    (h0 : ∫ ω, X 0 ω ∂μ = 0) (h1 : ∫ ω, (X 0 ω)^2 ∂μ = 1)
    (hind : iIndepFun X μ) (hid : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    {B : ℝ≥0 → Ω' → ℝ} (hB : IsBrownianReal B ν) :
    TendstoInDistribution (scaledWalk X) atTop (brownianPath B) (fun _ => μ) ν := by
  apply tendstoInDistribution_of_approximations
    (fun n => (scaledWalk_measurable X hXm n).aemeasurable) (brownianPath_aemeasurable hB)
    (A := fun m => coarseWalk X (m+1)) (B := fun m ω => pathApprox (m+1) (brownianPath B ω))
    (fun m => coarseWalk_CLT X h0 h1 hind hid hB (Nat.succ_pos m))
  intro δ hδ η hη
  obtain ⟨k,hk,hmod⟩ := iid_scaledWalk_modulus X hXm hX₂ hind hid h0 (half_pos hδ) hη
  have hb := (tendstoInMeasure_iff_measureReal_dist.mp
    (pathApprox_random_tendstoInMeasure (brownianPath B) (brownianPath_aemeasurable hB))) δ hδ
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hb.eventually (gt_mem_nhds hη))
  let m := max N (2*k)
  have hmk : 2*k ≤ m+1 := le_trans (le_max_right _ _) (Nat.le_succ _)
  have hNM : N ≤ m+1 := le_trans (le_max_left _ _) (Nat.le_succ _)
  have hmesh : 2/((m+1:ℕ):ℝ) ≤ 1/(k:ℝ) := by
    rw [div_le_div_iff₀ (Nat.cast_pos.mpr (Nat.succ_pos m)) (Nat.cast_pos.mpr hk),one_mul]
    exact_mod_cast hmk
  refine ⟨m,?_,?_⟩
  · filter_upwards [eventually_ge_atTop (max k ((m+1)*(m+1)))] with n hn
    apply le_trans (measureReal_mono ?_) (hmod n (le_trans (le_max_left _ _) hn))
    intro ω hω
    by_contra hh
    change ¬∃ s t : unitInterval, dist s t ≤ 1/(k:ℝ) ∧
      δ/2 < |scaledWalk X n ω s-scaledWalk X n ω t| at hh
    push Not at hh
    have he := coarseWalk_error_le X (Nat.succ_pos m) (le_trans (le_max_right _ _) hn) ω
      (half_pos hδ).le (fun s t hst => hh s t (hst.trans hmesh))
    have hd : dist (scaledWalk X n ω) (coarseWalk X (m+1) n ω) ≤ δ/2 := by
      rw [dist_comm,dist_eq_norm]
      exact he
    exact (not_lt_of_ge hω) (hd.trans_lt (half_lt_self hδ))
  · simpa only [dist_comm] using (hN (m+1) hNM).le

end FKCRT.TreeCoding
end

end OAI
