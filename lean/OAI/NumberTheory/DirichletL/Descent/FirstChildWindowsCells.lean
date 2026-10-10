import OAI.NumberTheory.DirichletL.Descent.FirstChildWindowsActual
import OAI.NumberTheory.DirichletL.Inversion.SecondSourceBlocks

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentFirstChildWindows
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels
open InverseSecondSourceBlocks (dyadIndex dyadScale dyadScale_pos dyadIndex_bounds)
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

abbrev SourceIndex := Fin 6→ℕ

def sourceNorms {κ : Type*} (A₁ A₂ C R : κ→ℝ) (d h : κ→O) (x : κ) : Fin 6→ℝ :=
  ![A₁ x,A₂ x,C x,‖eisEmbedding (d x)‖^2,R x,‖eisEmbedding (h x)‖^2]

def sourceIndex {κ : Type*} (q : κ→Fin 6→ℝ) (x : κ) : SourceIndex := fun i=>dyadIndex (q x i)
def sourceKeys {κ : Type*} [DecidableEq κ] (q : κ→Fin 6→ℝ) (S : Finset κ) := S.image (sourceIndex q)
def sourceCell {κ : Type*} [DecidableEq κ] (q : κ→Fin 6→ℝ) (S : Finset κ) (k : SourceIndex) :=
  S.filter (fun x=>sourceIndex q x=k)

def commonKeys {ι : Type*} [DecidableEq ι] (p : ι→O) (F : Finset ι) : Finset ℕ :=
  F.powerset.image (fun D=>dyadIndex (primeProductNorm p D))

def commonSelector {ι : Type*} [DecidableEq ι] (p : ι→O) (selector : Finset ι→ℂ) (l : ℕ) (D : Finset ι) : ℂ :=
  if dyadIndex (primeProductNorm p D)=l then selector D else 0

def rawScales (k : SourceIndex) (l : ℕ) (T₁ T₂ : ℝ) : Fin 9→ℝ :=
  ![dyadScale (k 0),dyadScale (k 1),dyadScale (k 2),dyadScale (k 3),dyadScale (k 4),
    dyadScale l,dyadScale (k 5),T₁,T₂]

lemma rawScales_pos (k : SourceIndex) (l : ℕ) (T₁ T₂ : ℝ) (h₁ : 0<T₁) (h₂ : 0<T₂) :
    ∀i,0<rawScales k l T₁ T₂ i := by
  intro i
  fin_cases i <;> first | exact dyadScale_pos _ | exact h₁ | exact h₂

lemma sourceNorms_ge_one {κ : Type*} (A₁ A₂ C R : κ→ℝ) (d h : κ→O) (x : κ)
    (hA₁ : 1≤A₁ x) (hA₂ : 1≤A₂ x) (hC : 1≤C x) (hR : 1≤R x)
    (hd : d x≠0) (hh : h x≠0) : ∀i,1≤sourceNorms A₁ A₂ C R d h x i := by
  intro i
  fin_cases i
  · exact hA₁
  · exact hA₂
  · exact hC
  · exact EisensteinSchwartzPoisson.one_le_eisenstein_norm_sq _ hd
  · exact hR
  · exact EisensteinSchwartzPoisson.one_le_eisenstein_norm_sq _ hh

lemma sourceCell_ratios {κ : Type*} [DecidableEq κ] (q : κ→Fin 6→ℝ) (S : Finset κ)
    (hq : ∀x∈S,∀i,1≤q x i) (k : SourceIndex) (x : κ) (hx : x∈sourceCell q S k) (i : Fin 6) :
    q x i/dyadScale (k i)∈Set.Icc 1 2 := by
  obtain ⟨hxs,hindex⟩ := Finset.mem_filter.mp hx
  have hh := dyadIndex_bounds (q x i) (hq x hxs i)
  have he : dyadIndex (q x i)=k i := congrFun hindex i
  rw [he] at hh
  exact ⟨(le_div_iff₀ (dyadScale_pos _)).mpr (by simpa using hh.1),
    (div_le_iff₀ (dyadScale_pos _)).mpr hh.2.le⟩

theorem actual_original_cell_ratios {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (S : Finset κ) (selector C₁ C₂ : κ→Finset ι→ℂ)
    (A₁ A₂ C R : κ→ℝ) (d h : κ→O)
    (hq : ∀x∈S,∀i,1≤sourceNorms A₁ A₂ C R d h x i)
    (k : SourceIndex) (l : ℕ) (T₁ T₂ : ℝ) (x : κ)
    (hx : x∈sourceCell (sourceNorms A₁ A₂ C R d h) S k) (j : FirstCommonIndex ι)
    (hn : commonSelector p (selector x) l j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) (h x) j≠0) :
    ∀i,actualOuterRatios p (A₁ x) (A₂ x) (C x) (R x) (d x) (h x) j (rawScales k l T₁ T₂) i∈Set.Icc 1 2 := by
  have hl : dyadIndex (primeProductNorm p j.2.1)=l := by
    by_contra he
    exact hn (by simp [commonSelector,he])
  have hh := dyadIndex_bounds _ (SecondPassArithmetic.primeProductNorm_ge_one p hp j.2.1)
  rw [hl] at hh
  have hD : primeProductNorm p j.2.1/dyadScale l∈Set.Icc 1 2 :=
    ⟨(le_div_iff₀ (dyadScale_pos _)).mpr (by simpa using hh.1),
      (div_le_iff₀ (dyadScale_pos _)).mpr hh.2.le⟩
  intro i
  fin_cases i
  · exact sourceCell_ratios _ S hq k x hx 0
  · exact sourceCell_ratios _ S hq k x hx 1
  · exact sourceCell_ratios _ S hq k x hx 2
  · exact sourceCell_ratios _ S hq k x hx 3
  · exact sourceCell_ratios _ S hq k x hx 4
  · exact hD
  · exact sourceCell_ratios _ S hq k x hx 5

lemma sum_source_cells {κ β : Type*} [DecidableEq κ] [AddCommMonoid β]
    (q : κ→Fin 6→ℝ) (S : Finset κ) (f : κ→β) :
    (∑x∈S,f x)=∑k∈sourceKeys q S,∑x∈sourceCell q S k,f x := by
  exact (Finset.sum_fiberwise_of_maps_to (fun x hx=>Finset.mem_image_of_mem (sourceIndex q) hx) f).symm

lemma common_key_of_index {ι : Type*} [DecidableEq ι] (p : ι→O) (F : Finset ι)
    (j : FirstCommonIndex ι) (hj : j∈firstCommonIndices F) :
    dyadIndex (primeProductNorm p j.2.1)∈commonKeys p F := by
  apply Finset.mem_image_of_mem
  exact (Finset.mem_sigma.mp (Finset.mem_product.mp hj).2).1

lemma sum_common_cells {ι : Type*} [DecidableEq ι] (p : ι→O) (F : Finset ι)
    (selector : Finset ι→ℂ) (G : FirstCommonIndex ι→ℂ) :
    (∑j∈firstCommonIndices F,selector j.2.1*G j)=
      ∑l∈commonKeys p F,∑j∈firstCommonIndices F,commonSelector p selector l j.2.1*G j := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  have hkey := common_key_of_index p F j hj
  simp [commonSelector,ite_mul,hkey]

theorem original_signed_partition {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (p : ι→O) (F : Finset ι) (S : Finset κ) (q : κ→Fin 6→ℝ)
    (selector : κ→Finset ι→ℂ) (G : κ→FirstCommonIndex ι→ℂ) :
    (∑x∈S,∑j∈firstCommonIndices F,selector x j.2.1*G x j)=
      ∑k∈sourceKeys q S,∑l∈commonKeys p F,∑x∈sourceCell q S k,
        ∑j∈firstCommonIndices F,commonSelector p (selector x) l j.2.1*G x j := by
  rw [sum_source_cells q S]
  apply Finset.sum_congr rfl
  intro k hk
  calc
    _ = ∑x∈sourceCell q S k,∑l∈commonKeys p F,
        ∑j∈firstCommonIndices F,commonSelector p (selector x) l j.2.1*G x j := by
      apply Finset.sum_congr rfl
      intro x hx
      exact sum_common_cells p F (selector x) (G x)
    _ = _ := Finset.sum_comm

end SevenEighths.InverseMomentFirstChildWindows
end

end OAI
