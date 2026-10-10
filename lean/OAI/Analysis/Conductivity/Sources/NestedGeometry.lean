import Mathlib
import OAI.Analysis.Conductivity.Model

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

def sourceScale : ℝ := 57/100
def sourceOffset : ℝ := 81/100
def sourceLength : ℝ := 8/5
def sourceHole : ℝ := 3/100

def sourceDomain : Set R3 := {x | sourceHole < max (|x 0|/sourceLength) |x 1| ∧
    max (|x 0|/sourceLength) |x 1| < 1 ∧ |x 2| < 1}

def sourceOuterBox : Set R3 := {x | |x 0| ≤ sourceLength ∧ |x 1| ≤ 1 ∧ |x 2| ≤ 1}

def sourceSwap : R3 ≃ₗᵢ[ℝ] R3 :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap (0:Fin 3) 1)

lemma sourceSwap_apply (x : R3) : sourceSwap x 0=x 1 ∧ sourceSwap x 1=x 0 ∧ sourceSwap x 2=x 2 := by
  change x ((Equiv.swap (0:Fin 3) 1).symm 0)=x 1 ∧
    x ((Equiv.swap (0:Fin 3) 1).symm 1)=x 0 ∧
    x ((Equiv.swap (0:Fin 3) 1).symm 2)=x 2
  simp [Equiv.symm_swap,Equiv.swap_apply_def]

def sourceShift (σ : ℝ) : R3 := EuclideanSpace.single 0 (σ*sourceOffset)

def sourceSimilarity (σ : ℝ) : R3 ≃ₜ R3 where
  toFun x := sourceScale • sourceSwap x+sourceShift σ
  invFun x := sourceSwap.symm (sourceScale⁻¹ • (x-sourceShift σ))
  left_inv x := by simp [sourceScale,smul_smul]
  right_inv x := by simp [sourceScale,smul_smul]
  continuous_toFun := (sourceSwap.continuous.const_smul sourceScale).add
    (continuous_const : Continuous (fun _ : R3 => sourceShift σ))
  continuous_invFun := sourceSwap.symm.continuous.comp
    ((continuous_id.sub (continuous_const : Continuous (fun _ : R3 => sourceShift σ))).const_smul sourceScale⁻¹)

lemma sourceSimilarity_coord (σ : ℝ) (x : R3) :
    sourceSimilarity σ x 0=sourceScale*x 1+σ*sourceOffset ∧
    sourceSimilarity σ x 1=sourceScale*x 0 ∧
    sourceSimilarity σ x 2=sourceScale*x 2 := by
  change (sourceScale • sourceSwap x+sourceShift σ) 0=_ ∧
    (sourceScale • sourceSwap x+sourceShift σ) 1=_ ∧
    (sourceScale • sourceSwap x+sourceShift σ) 2=_
  simp [sourceShift,PiLp.add_apply,PiLp.smul_apply,(sourceSwap_apply x).1,
    (sourceSwap_apply x).2.1,(sourceSwap_apply x).2.2]

lemma sourceSimilarity_dist (σ : ℝ) (x y : R3) :
    dist (sourceSimilarity σ x) (sourceSimilarity σ y)=sourceScale*dist x y := by
  change dist (sourceScale • sourceSwap x+sourceShift σ)
    (sourceScale • sourceSwap y+sourceShift σ)=_
  rw [dist_add_right,dist_smul₀,sourceSwap.dist_map]
  norm_num [sourceScale]

lemma sourceScale_rates : 0 < sourceScale ∧ sourceScale < 1 ∧ 1 < 2*sourceScale ∧
    2*sourceScale^3 < 1 := by norm_num [sourceScale]

lemma sourceDomain_isOpen : IsOpen sourceDomain := by
  have h₀ : Continuous (fun x : R3 => |x 0|/sourceLength) :=
    (EuclideanSpace.proj 0).continuous.abs.div_const _
  have h₁ : Continuous (fun x : R3 => |x 1|) := (EuclideanSpace.proj 1).continuous.abs
  have h₂ : Continuous (fun x : R3 => |x 2|) := (EuclideanSpace.proj 2).continuous.abs
  exact (isOpen_lt continuous_const (h₀.max h₁)).inter
    ((isOpen_lt (h₀.max h₁) continuous_const).inter (isOpen_lt h₂ continuous_const))

lemma sourceOuterBox_isClosed : IsClosed sourceOuterBox := by
  exact (isClosed_le (EuclideanSpace.proj 0).continuous.abs continuous_const).inter
    ((isClosed_le (EuclideanSpace.proj 1).continuous.abs continuous_const).inter
      (isClosed_le (EuclideanSpace.proj 2).continuous.abs continuous_const))

lemma sourceDomain_subset_box : sourceDomain⊆sourceOuterBox := by
  intro x hx
  have h₀ := (max_lt_iff.mp hx.2.1).1
  have h₁ := (max_lt_iff.mp hx.2.1).2
  refine ⟨?_,h₁.le,hx.2.2.le⟩
  dsimp [sourceLength] at *
  linarith

lemma sourceClosure_subset_box : closure sourceDomain⊆sourceOuterBox :=
  closure_minimal sourceDomain_subset_box sourceOuterBox_isClosed

lemma sourceBox_norm_bound {x : R3} (hx : x∈sourceOuterBox) : ‖x‖ < 5/2 := by
  have hn := EuclideanSpace.real_norm_sq_eq x
  simp [Fin.sum_univ_succ] at hn
  have h₀ := abs_le.mp hx.1
  have h₁ := abs_le.mp hx.2.1
  have h₂ := abs_le.mp hx.2.2
  dsimp [sourceLength] at h₀
  have hq₀ : (x 0)^2 ≤ (8/5:ℝ)^2 := by
    have hh : |x 0|^2 ≤ (8/5:ℝ)^2 := (sq_le_sq₀ (abs_nonneg _) (by norm_num)).mpr hx.1
    simpa only [sq_abs] using hh
  have hq₁ : (x 1)^2 ≤ 1 := by nlinarith [sq_le_sq₀ (abs_nonneg (x 1)) (by norm_num : (0:ℝ) ≤ 1) |>.mpr hx.2.1]
  have hq₂ : (x 2)^2 ≤ 1 := by nlinarith [sq_le_sq₀ (abs_nonneg (x 2)) (by norm_num : (0:ℝ) ≤ 1) |>.mpr hx.2.2]
  nlinarith [norm_nonneg x]

lemma sourceClosure_subset_ball : closure sourceDomain⊆Metric.ball (0:R3) (5/2) := by
  intro x hx
  simpa only [Metric.mem_ball,dist_zero_right] using sourceBox_norm_bound (sourceClosure_subset_box hx)

lemma sourceDomain_isBounded : Bornology.IsBounded sourceDomain :=
  (Metric.isBounded_ball (x := (0:R3)) (r := (5/2:ℝ))).subset
    (fun _ hx => sourceClosure_subset_ball (subset_closure hx))

lemma sourceClosure_isCompact : IsCompact (closure sourceDomain) :=
  (Metric.isCompact_iff_isClosed_bounded).mpr ⟨isClosed_closure,sourceDomain_isBounded.closure⟩

lemma source_children_coords {x : R3} (hx : x∈sourceOuterBox) :
    (24/100:ℝ) ≤ sourceSimilarity 1 x 0 ∧ sourceSimilarity 1 x 0 ≤ 138/100 ∧
    -(138/100:ℝ) ≤ sourceSimilarity (-1) x 0 ∧ sourceSimilarity (-1) x 0 ≤ -(24/100:ℝ) ∧
    |sourceSimilarity 1 x 1| ≤ 912/1000 ∧ |sourceSimilarity (-1) x 1| ≤ 912/1000 ∧
    |sourceSimilarity 1 x 2| ≤ 57/100 ∧ |sourceSimilarity (-1) x 2| ≤ 57/100 := by
  have h₀ := abs_le.mp hx.1
  have h₁ := abs_le.mp hx.2.1
  have h₂ := abs_le.mp hx.2.2
  rw [(sourceSimilarity_coord 1 x).1,(sourceSimilarity_coord (-1) x).1,
    (sourceSimilarity_coord 1 x).2.1,(sourceSimilarity_coord (-1) x).2.1,
    (sourceSimilarity_coord 1 x).2.2,(sourceSimilarity_coord (-1) x).2.2]
  simp only [abs_mul,sourceScale,sourceOffset,abs_of_pos (by norm_num : (0:ℝ) < 57/100)]
  dsimp [sourceLength] at h₀
  constructor; · linarith
  constructor; · linarith
  constructor; · linarith
  constructor; · linarith
  constructor; · have hh : |x 0| ≤ (8/5:ℝ) := hx.1; linarith
  constructor; · have hh : |x 0| ≤ (8/5:ℝ) := hx.1; linarith
  constructor <;> linarith [hx.2.2]

lemma source_positive_child_in_parent {x : R3} (hx : x∈sourceOuterBox) :
    sourceSimilarity 1 x∈sourceDomain := by
  obtain ⟨hmin,hmax,_,_,hy,_,hz,_⟩ := source_children_coords hx
  have hpos : 0 ≤ sourceSimilarity 1 x 0 := by linarith
  change sourceHole < max _ _ ∧ max _ _ < 1 ∧ _
  refine ⟨lt_of_lt_of_le ?_ (le_max_left _ _),max_lt ?_ ?_,?_⟩
  · rw [abs_of_nonneg hpos]; norm_num [sourceHole,sourceLength]; linarith
  · rw [abs_of_nonneg hpos]; norm_num [sourceLength]; linarith
  · linarith
  · linarith

lemma source_negative_child_in_parent {x : R3} (hx : x∈sourceOuterBox) :
    sourceSimilarity (-1) x∈sourceDomain := by
  obtain ⟨_,_,hmin,hmax,_,hy,_,hz⟩ := source_children_coords hx
  have hneg : sourceSimilarity (-1) x 0 ≤ 0 := by linarith
  change sourceHole < max _ _ ∧ max _ _ < 1 ∧ _
  refine ⟨lt_of_lt_of_le ?_ (le_max_left _ _),max_lt ?_ ?_,?_⟩
  · rw [abs_of_nonpos hneg]; norm_num [sourceHole,sourceLength]; linarith
  · rw [abs_of_nonpos hneg]; norm_num [sourceLength]; linarith
  · linarith
  · linarith

theorem source_children_compact_inside :
    IsCompact (sourceSimilarity 1 '' closure sourceDomain) ∧
    IsCompact (sourceSimilarity (-1) '' closure sourceDomain) ∧
    sourceSimilarity 1 '' closure sourceDomain⊆sourceDomain ∧
    sourceSimilarity (-1) '' closure sourceDomain⊆sourceDomain ∧
    Disjoint (sourceSimilarity 1 '' closure sourceDomain)
      (sourceSimilarity (-1) '' closure sourceDomain) := by
  refine ⟨sourceClosure_isCompact.image (sourceSimilarity 1).continuous,
    sourceClosure_isCompact.image (sourceSimilarity (-1)).continuous,?_,?_,?_⟩
  · rintro _ ⟨x,hx,rfl⟩
    exact source_positive_child_in_parent (sourceClosure_subset_box hx)
  · rintro _ ⟨x,hx,rfl⟩
    exact source_negative_child_in_parent (sourceClosure_subset_box hx)
  · rw [Set.disjoint_left]
    rintro _ ⟨x,hx,rfl⟩ ⟨y,hy,he⟩
    have h₁ := (source_children_coords (sourceClosure_subset_box hx)).1
    have h₂ := (source_children_coords (sourceClosure_subset_box hy)).2.2.2.1
    have hh := congrArg (fun p : R3 => p 0) he
    linarith

end ScalarConductivity

end

end OAI
