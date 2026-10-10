import OAI.Combinatorics.InfiniteMatroid.Reservations
import OAI.Combinatorics.InfiniteMatroid.BasisExtension

namespace OAI

section
open Set Filter
open scoped Topology symmDiff
namespace InfiniteMatroidCounterexample

def slice (X : Set E0) (b : Bool) : Set D := {d | (d,b) ∈ X}
@[simp] lemma slice_compl (X : Set E0) (b : Bool) : slice Xᶜ b = (slice X b)ᶜ := rfl
@[simp] lemma slice_symmDiff (X Y : Set E0) (b : Bool) : slice (X ∆ Y) b = slice X b ∆ slice Y b := rfl
@[simp] lemma slice_empty (b : Bool) : slice ∅ b = ∅ := rfl
@[simp] lemma slice_univ (b : Bool) : slice univ b = univ := rfl
lemma slice_mono {X Y : Set E0} (h : X ⊆ Y) (b : Bool) : slice X b ⊆ slice Y b := fun _ hx ↦ h hx
lemma subset_iff_slice {X Y : Set E0} : X ⊆ Y ↔ ∀ b, slice X b ⊆ slice Y b := by
  constructor
  · exact slice_mono
  · intro h x hx; exact h x.2 hx

def joinSlices (u v : Set D) : Set E0 := {x | if x.2 then x.1 ∈ v else x.1 ∈ u}
@[simp] lemma slice_join_false (u v : Set D) : slice (joinSlices u v) false = u := by ext; simp [slice,joinSlices]
@[simp] lemma slice_join_true (u v : Set D) : slice (joinSlices u v) true = v := by ext; simp [slice,joinSlices]

lemma density_slice_le (X : Set E0) (b : Bool) (m : ℕ) : dDensity (slice X b) m ≤ 2 * density X m := by
  classical
  have hi : Function.Injective (fun d : D ↦ (d,b)) := fun _ _ h ↦ congrArg Prod.fst h
  have hs : (traceFinset (dBlock m) (slice X b)).image (fun d ↦ (d,b)) ⊆ traceFinset (wBlock m) X := by
    intro x hx
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hdm,hdX⟩ := (mem_traceFinset _ _ _).mp hd
    exact (mem_traceFinset _ _ _).mpr ⟨Finset.mem_product.mpr ⟨hdm,Finset.mem_univ _⟩,hdX⟩
  have hc : ((traceFinset (dBlock m) (slice X b)).card : ℝ) ≤ (traceFinset (wBlock m) X).card := by
    exact_mod_cast ((Finset.card_image_of_injective _ hi) ▸ Finset.card_le_card hs)
  have hw : (0:ℝ) < 2 ^ (2 ^ m) := by positivity
  unfold dDensity density finiteDensity
  rw [card_dBlock,card_wBlock]
  push_cast
  have he (a : ℝ) : 2 * (a / (2 * 2 ^ (2 ^ m))) = a / 2 ^ (2 ^ m) := by ring
  rw [he]
  exact div_le_div_of_nonneg_right hc hw.le

lemma small_slice {X : Set E0} (h : Small X) (b : Bool) : DSmall (slice X b) := by
  have ht : Tendsto (fun m ↦ 2 * density X m) atTop (𝓝 0) := by simpa using h.const_mul 2
  exact squeeze_zero (fun m ↦ finiteDensity_nonneg _ _) (density_slice_le X b) ht

def KSmall0 (X : Set E0) : Prop := ∀ b, KSmall (slice X b)
lemma small_kSmall0 {X : Set E0} (h : Small X) : KSmall0 X := fun b ↦ dSmall_kSmall (small_slice h b)
lemma kSmall0_mono {X Y : Set E0} (hY : KSmall0 Y) (hXY : X ⊆ Y) : KSmall0 X :=
  fun b ↦ kSmall_mono (hY b) (slice_mono hXY b)
lemma kSmall0_union {X Y : Set E0} (hX : KSmall0 X) (hY : KSmall0 Y) : KSmall0 (X ∪ Y) :=
  fun b ↦ kSmall_union (hX b) (hY b)
lemma hCell_kSmall0 (t : CIndex) (k : Bool) : KSmall0 (HCell t k) := by
  intro b
  exact kSmall_mono (AColumn_compl_kSmall t) (dCell_subset_Acompl t k)

namespace RankModel
variable (R : RankModel D)

def Admissible (X : Set E0) : Prop :=
  (slice X false ∈ R.ultra ∧ (slice X true)ᶜ ∈ R.ultra ∧
    R.rank (slice X true)ᶜ < R.rank (slice X false)) ∨
  (slice X false ∉ R.ultra ∧ (slice X true)ᶜ ∉ R.ultra ∧
    R.rank (slice X true) < R.rank (slice X false)ᶜ)
def Upper (X : Set E0) : Prop :=
  slice X false ∈ R.ultra ∧ ((slice X true)ᶜ ∉ R.ultra ∨
    ((slice X true)ᶜ ∈ R.ultra ∧ R.rank (slice X false) ≤ R.rank (slice X true)ᶜ))
def Lower (X : Set E0) : Prop := R.Upper Xᶜ

lemma admissible_iff (X : Set E0) : R.Admissible X ↔ ¬ R.Upper X ∧ ¬ R.Lower X := by
  by_cases hu : slice X false ∈ R.ultra <;> by_cases hy : (slice X true)ᶜ ∈ R.ultra <;>
    simp_all [Admissible,Upper,Lower,Ultrafilter.compl_mem_iff_notMem,not_le]

lemma admissible_compl {X : Set E0} (h : R.Admissible X) : R.Admissible Xᶜ := by
  rw [R.admissible_iff] at h ⊢
  simpa only [Lower,compl_compl,and_comm] using h

lemma upper_mono {X Y : Set E0} (hX : R.Upper X) (hXY : X ⊆ Y) : R.Upper Y := by
  have hu : slice Y false ∈ R.ultra := mem_of_superset hX.1 (slice_mono hXY false)
  refine ⟨hu,?_⟩
  by_cases hy : (slice Y true)ᶜ ∈ R.ultra
  · have hyX : (slice X true)ᶜ ∈ R.ultra := mem_of_superset hy (compl_subset_compl.mpr (slice_mono hXY true))
    have hr := hX.2.resolve_left (not_not.mpr hyX)
    refine Or.inr ⟨hy,?_⟩
    exact (R.antitone hX.1 hu (R.ideal.modSubset_of_subset (slice_mono hXY false))).trans
      ((hr.2).trans (R.antitone hy hyX (R.ideal.modSubset_of_subset (compl_subset_compl.mpr (slice_mono hXY true)))))
  · exact Or.inl hy

lemma lower_mono {X Y : Set E0} (hY : R.Lower Y) (hXY : X ⊆ Y) : R.Lower X :=
  R.upper_mono hY (compl_subset_compl.mpr hXY)

lemma upper_univ : R.Upper univ := by
  simpa [Upper] using (show (Set.univ : Set D) ∈ R.ultra from Filter.univ_mem)
lemma lower_empty : R.Lower ∅ := by simpa [Lower] using R.upper_univ
lemma upper_not_lower {X : Set E0} (hX : R.Upper X) : ¬ R.Lower X := by
  intro hL
  have hu : (slice X false)ᶜ ∈ R.ultra := hL.1
  exact (Ultrafilter.compl_mem_iff_notMem.mp hu) hX.1
lemma not_upper_empty : ¬ R.Upper ∅ := by simp [Upper]
lemma not_lower_univ : ¬ R.Lower univ := by simpa [Lower] using R.not_upper_empty

variable (hK : R.ideal = KIdeal)
include hK
lemma status_invariant {X Y : Set E0} (h : KSmall0 (X ∆ Y)) :
    (R.Upper X ↔ R.Upper Y) ∧ (R.Lower X ↔ R.Lower Y) ∧
      (R.Admissible X ↔ R.Admissible Y) := by
  have hu : R.ideal.small (slice X false ∆ slice Y false) := by rw [hK]; exact h false
  have hv : R.ideal.small (slice X true ∆ slice Y true) := by rw [hK]; exact h true
  have huc : R.ideal.small ((slice X false)ᶜ ∆ (slice Y false)ᶜ) := by
    convert hu using 1
    ext x; simp only [Set.mem_symmDiff,Set.mem_compl_iff]; tauto
  have hvc : R.ideal.small ((slice X true)ᶜ ∆ (slice Y true)ᶜ) := by
    convert hv using 1
    ext x; simp only [Set.mem_symmDiff,Set.mem_compl_iff]; tauto
  obtain ⟨heu,hru⟩ := R.invariant hu
  obtain ⟨hev,hrv⟩ := R.invariant hv
  obtain ⟨heuc,hruc⟩ := R.invariant huc
  obtain ⟨hevc,hrvc⟩ := R.invariant hvc
  have hUp : R.Upper X ↔ R.Upper Y := by
    constructor
    · rintro ⟨hu,hv | ⟨hv,hr⟩⟩
      · exact ⟨heu.mp hu,Or.inl (fun hy ↦ hv (hevc.mpr hy))⟩
      · exact ⟨heu.mp hu,Or.inr ⟨hevc.mp hv,by rwa [← hru hu,← hrvc hv]⟩⟩
    · rintro ⟨hu,hv | ⟨hv,hr⟩⟩
      · exact ⟨heu.mpr hu,Or.inl (fun hx ↦ hv (hevc.mp hx))⟩
      · exact ⟨heu.mpr hu,Or.inr ⟨hevc.mpr hv,by rwa [hru (heu.mpr hu),hrvc (hevc.mpr hv)]⟩⟩
  have hLo : R.Lower X ↔ R.Lower Y := by
    simp only [Lower,Upper,slice_compl,compl_compl]
    constructor
    · rintro ⟨hu,hv | ⟨hv,hr⟩⟩
      · exact ⟨heuc.mp hu,Or.inl (fun hy ↦ hv (hev.mpr hy))⟩
      · exact ⟨heuc.mp hu,Or.inr ⟨hev.mp hv,by rwa [← hruc hu,← hrv hv]⟩⟩
    · rintro ⟨hu,hv | ⟨hv,hr⟩⟩
      · exact ⟨heuc.mpr hu,Or.inl (fun hx ↦ hv (hev.mp hx))⟩
      · exact ⟨heuc.mpr hu,Or.inr ⟨hev.mpr hv,by rwa [hruc (heuc.mpr hu),hrv (hev.mpr hv)]⟩⟩
  exact ⟨hUp,hLo,by rw [R.admissible_iff,R.admissible_iff,hUp,hLo]⟩

lemma admissible_positive {X : Set E0} (hX : R.Admissible X) : ¬ Small X := by
  intro hs
  have hl (b : Bool) : slice X b ∉ R.ultra := R.avoids _ (by rw [hK]; exact small_kSmall0 hs b)
  rcases hX with ⟨hu,_,_⟩ | ⟨_,hy,_⟩
  · exact hl false hu
  · exact hy (Ultrafilter.compl_mem_iff_notMem.mpr (hl true))

lemma admissible_sameClass {T X : Set E0} (hT : R.Admissible T) (hX : SameClass T X) : R.Admissible X :=
  ((R.status_invariant hK (small_kSmall0 hX)).2.2).mpr hT

end RankModel
namespace RankModel
variable (R : RankModel D)

lemma zone_crossing {A Z : Set E0} (hAZ : A ⊆ Z) (hA : R.Lower A) (hZ : R.Upper Z) :
    ∃ B, A ⊆ B ∧ B ⊆ Z ∧ R.Admissible B := by
  have hs : slice A false ∉ R.ultra := Ultrafilter.compl_mem_iff_notMem.mp hA.1
  have hX : slice Z false ∈ R.ultra := hZ.1
  have hsX := slice_mono hAZ false
  by_cases hy : (slice A true)ᶜ ∈ R.ultra
  · obtain ⟨u,hsu,huX,hu,hru⟩ := R.thinning _ _ hsX hs hX (R.rank (slice A true)ᶜ)
    refine ⟨joinSlices u (slice A true),?_,?_,Or.inl ?_⟩
    · rw [subset_iff_slice]
      intro b; cases b
      · simpa using hsu
      · simp
    · rw [subset_iff_slice]
      intro b; cases b
      · simpa using huX
      · simpa using slice_mono hAZ true
    · simpa only [slice_join_false,slice_join_true] using And.intro hu (And.intro hy hru)
  · have hs' : (slice Z false)ᶜ ∉ R.ultra := fun h ↦ (Ultrafilter.compl_mem_iff_notMem.mp h) hX
    have hX' : (slice A false)ᶜ ∈ R.ultra := Ultrafilter.compl_mem_iff_notMem.mpr hs
    obtain ⟨v,hZv,hvA,hv,hrv⟩ := R.thinning _ _ (compl_subset_compl.mpr hsX) hs' hX'
      (R.rank (slice A true))
    refine ⟨joinSlices vᶜ (slice A true),?_,?_,Or.inr ?_⟩
    · rw [subset_iff_slice]
      intro b; cases b
      · simpa using compl_subset_compl.mpr hvA
      · simp
    · rw [subset_iff_slice]
      intro b; cases b
      · simpa using compl_subset_compl.mpr hZv
      · simpa using slice_mono hAZ true
    · have hvc : vᶜ ∉ R.ultra := fun h ↦ (Ultrafilter.compl_mem_iff_notMem.mp h) hv
      simpa only [slice_join_false,slice_join_true,compl_compl] using And.intro hvc (And.intro hy hrv)

lemma exists_admissible_between {A Z : Set E0} (hAZ : A ⊆ Z) (hA : ¬ R.Upper A) (hZ : ¬ R.Lower Z) :
    ∃ B, A ⊆ B ∧ B ⊆ Z ∧ R.Admissible B := by
  by_cases ha : R.Admissible A
  · exact ⟨A,Subset.rfl,hAZ,ha⟩
  by_cases hz : R.Admissible Z
  · exact ⟨Z,hAZ,Subset.rfl,hz⟩
  have hAL : R.Lower A := by
    by_contra h
    exact ha ((R.admissible_iff A).mpr ⟨hA,h⟩)
  have hZU : R.Upper Z := by
    by_contra h
    exact hz ((R.admissible_iff Z).mpr ⟨h,hZ⟩)
  exact R.zone_crossing hAZ hAL hZU

end RankModel
end InfiniteMatroidCounterexample
end

end OAI
