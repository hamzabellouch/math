import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTFrequencyCover

namespace OAI

/-! A bounded measurable frequency set can be sampled in two separated
classes. Sample points stay in the original set, so its large-value witnesses
are preserved without taking a neighbourhood or differentiating them. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

lemma mrt_unit_cell_sample (G : ℝ → ℝ) (hG : Continuous G)
    (hG0 : ∀ t, 0 ≤ G t) {E : Set ℝ} (hE : MeasurableSet E)
    (a : ℝ) (hsub : E ⊆ Set.Ioc a (a+1)) (hne : E.Nonempty) :
    ∃ t ∈ E, (∫ u in E, G u) ≤ 2*G t := by
  have hab : a ≤ a+1 := by linarith
  have hiI : IntegrableOn G (Set.Ioc a (a+1)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp
    (hG.intervalIntegrable a (a+1))
  have hi := hiI.mono_set hsub
  by_contra hn
  push Not at hn
  let C := ∫ u in E, G u
  have hC : 0 < C := by
    obtain ⟨t,ht⟩ := hne
    have hh := hn t ht
    dsimp only [C]
    linarith [hG0 t]
  have hiConst : IntegrableOn (fun _ : ℝ => C/2) (Set.Ioc a (a+1)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp
    ((continuous_const : Continuous (fun _ : ℝ => C/2)).intervalIntegrable a (a+1))
  have hc : C ≤ C/2 := by
    calc
      _ ≤ ∫ u in E, C/2 := setIntegral_mono_on hi (hiConst.mono_set hsub) hE
        (fun t ht => by have hh := hn t ht; change 2*G t < C at hh; linarith)
      _ ≤ ∫ u in Set.Ioc a (a+1), C/2 := setIntegral_mono_set hiConst
        (Filter.Eventually.of_forall (fun _ => by change 0 ≤ C/2; positivity))
        (Filter.Eventually.of_forall hsub)
      _ = _ := by
        rw [← intervalIntegral.integral_of_le hab, intervalIntegral.integral_const]
        simp
  linarith

lemma mrt_cell_sample_injective (J : Finset ℕ) (a : ℝ) (x : ℕ → ℝ)
    (hx : ∀ k ∈ J, x k ∈ Set.Ioc (a+k) (a+k+1)) :
    Set.InjOn x J := by
  intro k hk l hl hkl
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hn : (k:ℝ)+1 ≤ l := by exact_mod_cast hlt
    have h1 := hx k hk
    have h2 := hx l hl
    rw [hkl] at h1
    linarith [h1.2,h2.1]
  · have hn : (l:ℝ)+1 ≤ k := by exact_mod_cast hlt
    have h1 := hx k hk
    have h2 := hx l hl
    rw [hkl] at h1
    linarith [h1.1,h2.2]

lemma mrt_cell_sample_separated (J : Finset ℕ) (a : ℝ) (x : ℕ → ℝ)
    (hx : ∀ k ∈ J, x k ∈ Set.Ioc (a+k) (a+k+1))
    (hpar : ∀ k ∈ J, ∀ l ∈ J, k%2 = l%2) :
    ∀ t ∈ J.image x, ∀ s ∈ J.image x, t≠s → 1 ≤ |t-s| := by
  intro t ht s hs hts
  obtain ⟨k,hk,rfl⟩ := mem_image.mp ht
  obtain ⟨l,hl,rfl⟩ := mem_image.mp hs
  have hne : k≠l := fun h => hts (congrArg x h)
  have hmod := hpar k hk l hl
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hnat : k+2 ≤ l := by omega
    have hcast : (k:ℝ)+2 ≤ l := by exact_mod_cast hnat
    have h1 := hx k hk
    have h2 := hx l hl
    rw [abs_of_nonpos (by linarith [h1.2,h2.1] : x k-x l ≤ 0)]
    linarith [h1.2,h2.1]
  · have hnat : l+2 ≤ k := by omega
    have hcast : (l:ℝ)+2 ≤ k := by exact_mod_cast hnat
    have h1 := hx k hk
    have h2 := hx l hl
    rw [abs_of_nonneg (by linarith [h1.1,h2.2] : 0 ≤ x k-x l)]
    linarith [h1.1,h2.2]

/-- A uniform bound on all separated samples gives a bound on the actual
set integral, with the sample points still lying in that set. -/
theorem mrt_set_integral_of_samples (G : ℝ → ℝ) (hG : Continuous G)
    (hG0 : ∀ t, 0 ≤ G t) {E : Set ℝ} (hE : MeasurableSet E)
    {T B : ℝ} (hT : 0 ≤ T) (hET : E ⊆ Set.Ioc (-T) T)
    (hsamples : ∀ S : Finset ℝ, (∀ t ∈ S, t ∈ E) →
      (∀ t ∈ S, ∀ s ∈ S, t≠s → 1 ≤ |t-s|) → ∑ t ∈ S, G t ≤ B) :
    (∫ t in E, G t) ≤ 4*B := by
  let N := ⌈2*T⌉₊
  let cell := fun k : ℕ => Set.Ioc (-T+k) (-T+k+1)
  let J := (range N).filter (fun k => (E ∩ cell k).Nonempty)
  have hselect (k : ℕ) (hk : k ∈ J) :
      ∃ t ∈ E ∩ cell k, (∫ u in E ∩ cell k, G u) ≤ 2*G t :=
    mrt_unit_cell_sample G hG hG0 (hE.inter measurableSet_Ioc) (-T+k)
      Set.inter_subset_right (mem_filter.mp hk).2
  let x := fun k => if hk : k ∈ J then Classical.choose (hselect k hk) else 0
  have hx (k : ℕ) (hk : k ∈ J) : x k ∈ E ∩ cell k ∧
      (∫ u in E ∩ cell k, G u) ≤ 2*G (x k) := by
    simpa only [x, dite_eq_left hk] using Classical.choose_spec (hselect k hk)
  have hcover (t : ℝ) (ht : t ∈ E) : ∃ k ∈ range N, t ∈ cell k := by
    have ht' := hET ht
    have hpos : 0 < t+T := by linarith [ht'.1]
    have hcpos : 0 < ⌈t+T⌉₊ := Nat.ceil_pos.mpr hpos
    have hcN : ⌈t+T⌉₊ ≤ N := Nat.ceil_mono (by linarith [ht'.2])
    let k := ⌈t+T⌉₊-1
    have hsucc : k+1 = ⌈t+T⌉₊ := by dsimp [k]; omega
    have hcast : (k:ℝ)+1 = (⌈t+T⌉₊:ℝ) := by exact_mod_cast hsucc
    refine ⟨k,mem_range.mpr (by omega),?_⟩
    have hlo := Nat.ceil_lt_add_one hpos.le
    have hhi := Nat.le_ceil (t+T)
    change -T+(k:ℝ) < t ∧ t ≤ -T+(k:ℝ)+1
    constructor <;> linarith
  have hi : IntegrableOn G (Set.Ioc (-T) T) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : -T ≤ T)).mp
    (hG.intervalIntegrable (-T) T)
  have hc := mrt_nonnegative_integral_cover (range N) cell
    (fun _ _ => measurableSet_Ioc) hE G (hi.mono_set hET)
    (fun t _ => hG0 t) hcover
  have he : (∑ k ∈ range N, ∫ t in E ∩ cell k, G t) =
      ∑ k ∈ J, ∫ t in E ∩ cell k, G t := by
    symm
    apply sum_subset (filter_subset _ _)
    intro k hk hkJ
    have hn : ¬(E ∩ cell k).Nonempty := fun h => hkJ (mem_filter.mpr ⟨hk,h⟩)
    rw [Set.not_nonempty_iff_eq_empty.mp hn]
    simp
  rw [he] at hc
  have hp (I : Finset ℕ) (hIJ : I ⊆ J)
      (hpar : ∀ k ∈ I, ∀ l ∈ I, k%2=l%2) : (∑ k ∈ I, G (x k)) ≤ B := by
    have hcell (k : ℕ) (hk : k ∈ I) : x k ∈ cell k := (hx k (hIJ hk)).1.2
    have hbound := hsamples (I.image x)
      (fun t ht => by obtain ⟨k,hk,rfl⟩ := mem_image.mp ht; exact (hx k (hIJ hk)).1.1)
      (mrt_cell_sample_separated I (-T) x hcell hpar)
    rw [sum_image (mrt_cell_sample_injective I (-T) x hcell)] at hbound
    exact hbound
  have h0 := hp (J.filter (fun k => k%2=0)) (filter_subset _ _)
    (fun k hk l hl => (mem_filter.mp hk).2.trans (mem_filter.mp hl).2.symm)
  have h1 := hp (J.filter (fun k => ¬k%2=0)) (filter_subset _ _)
    (fun k hk l hl => by have hkm := (mem_filter.mp hk).2; have hlm := (mem_filter.mp hl).2; omega)
  have hs : (∑ k ∈ J, G (x k)) ≤ 2*B := by
    have he := sum_filter_add_sum_filter_not J (fun k => k%2=0) (fun k => G (x k))
    linarith
  calc
    _ ≤ ∑ k ∈ J, ∫ t in E ∩ cell k, G t := hc
    _ ≤ ∑ k ∈ J, 2*G (x k) := sum_le_sum (fun k hk => (hx k hk).2)
    _ = 2*∑ k ∈ J, G (x k) := (mul_sum _ _ _).symm
    _ ≤ 4*B := by linarith

end TwoPointCorrelations

end OAI
