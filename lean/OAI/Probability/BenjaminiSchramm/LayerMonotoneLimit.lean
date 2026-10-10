import OAI.Probability.BenjaminiSchramm.SlabCountBasic
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

lemma restrictedLayerCount_mono_vertices {A B : Set V} (hAB : A ⊆ B)
    (I : Set E) (ω : Set E) (x : V) :
    restrictedLayerCount G I A ω x ≤ restrictedLayerCount G I B ω x := by
  apply ENNReal.tsum_le_tsum
  intro y
  by_cases hy : y ∈ A ∧ Conn G (ω ∩ I) x y
  · rw [ite_eq_left hy,ite_eq_left ⟨hAB hy.1,hy.2⟩]
  · rw [ite_eq_right hy]
    exact bot_le

lemma internalEdges_lowerSlabs_iUnion (f : V → ℝ) (R c : ℝ) (hR : 0 < R) :
    (⋃ n : ℕ, internalEdges G {z | -(n : ℝ)*R ≤ f z ∧ f z ≤ c})=
      internalEdges G {z | f z ≤ c} := by
  ext e
  constructor
  · rintro ⟨_,⟨n,rfl⟩,hn⟩
    exact internalEdges_mono G (fun _ hz => hz.2) hn
  · intro he
    have hpair : ∀ s : Sym2 V, (∀ z ∈ s, f z ≤ c) →
        ∃ n : ℕ, ∀ z ∈ s, -(n : ℝ)*R ≤ f z ∧ f z ≤ c := by
      intro s
      induction s using Sym2.inductionOn with
      | _ u v =>
        intro hs
        obtain ⟨N,hN⟩ := exists_nat_gt (max (-f u/R) (-f v/R))
        refine ⟨N,fun z hz => ?_⟩
        have hNu : -f u < (N : ℝ)*R :=
          (div_lt_iff₀ hR).mp ((le_max_left _ _).trans_lt hN)
        have hNv : -f v < (N : ℝ)*R :=
          (div_lt_iff₀ hR).mp ((le_max_right _ _).trans_lt hN)
        rcases Sym2.mem_iff.mp hz with rfl | rfl
        · exact ⟨by linarith,hs z hz⟩
        · exact ⟨by linarith,hs z hz⟩
    obtain ⟨n,hn⟩ := hpair (G e) he
    exact mem_iUnion.mpr ⟨n,hn⟩

lemma internalEdges_lowerSlabs_monotone (f : V → ℝ) (R c : ℝ) (hR : 0 ≤ R) :
    Monotone (fun n : ℕ => internalEdges G {z | -(n : ℝ)*R ≤ f z ∧ f z ≤ c}) := by
  intro n m hnm
  apply internalEdges_mono G
  intro z hz
  have hh := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hnm : (n : ℝ) ≤ m) hR
  exact ⟨by linarith [hz.1],hz.2⟩

lemma internalEdges_lowerSlabs_shift_iUnion (f : V → ℝ) (R c b : ℝ) (hR : 0 < R) :
    (⋃ n : ℕ, internalEdges G {z | b-(n : ℝ)*R ≤ f z ∧ f z ≤ c})=
      internalEdges G {z | f z ≤ c} := by
  have he (n : ℕ) : {z | -(n : ℝ)*R ≤ f z-b ∧ f z-b ≤ c-b}=
      {z | b-(n : ℝ)*R ≤ f z ∧ f z ≤ c} := by
    ext z
    constructor <;> intro hz <;> constructor <;> linarith [hz.1,hz.2]
  have hc : {z | f z-b ≤ c-b}={z | f z ≤ c} := by
    ext z
    change (f z-b ≤ c-b) ↔ f z ≤ c
    constructor <;> intro hz <;> linarith
  simpa only [he,hc] using internalEdges_lowerSlabs_iUnion G (fun z => f z-b) R (c-b) hR

lemma internalEdges_lowerSlabs_shift_monotone (f : V → ℝ) (R c b : ℝ) (hR : 0 ≤ R) :
    Monotone (fun n : ℕ => internalEdges G {z | b-(n : ℝ)*R ≤ f z ∧ f z ≤ c}) := by
  intro n j hnj
  apply internalEdges_mono G
  intro z hz
  have hh := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hnj : (n : ℝ) ≤ j) hR
  exact ⟨by linarith [hz.1],hz.2⟩

lemma internalEdges_upperSlabs_iUnion (f : V → ℝ) (R m b : ℝ) (hR : 0 < R) :
    (⋃ n : ℕ, internalEdges G {z | m ≤ f z ∧ f z ≤ b+(n : ℝ)*R})=
      internalEdges G {z | m ≤ f z} := by
  have he (n : ℕ) : {z | -(n : ℝ)*R ≤ -f z+b ∧ -f z+b ≤ -m+b}=
      {z | m ≤ f z ∧ f z ≤ b+(n : ℝ)*R} := by
    ext z
    constructor <;> intro hz <;> constructor <;> linarith [hz.1,hz.2]
  have hc : {z | -f z+b ≤ -m+b}={z | m ≤ f z} := by
    ext z
    change (-f z+b ≤ -m+b) ↔ m ≤ f z
    constructor <;> intro hz <;> linarith
  simpa only [he,hc] using internalEdges_lowerSlabs_iUnion G (fun z => -f z+b) R (-m+b) hR

lemma internalEdges_upperSlabs_monotone (f : V → ℝ) (R m b : ℝ) (hR : 0 ≤ R) :
    Monotone (fun n : ℕ => internalEdges G {z | m ≤ f z ∧ f z ≤ b+(n : ℝ)*R}) := by
  intro n j hnj
  apply internalEdges_mono G
  intro z hz
  have hh := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hnj : (n : ℝ) ≤ j) hR
  exact ⟨hz.1,by linarith [hz.2]⟩

variable [Countable V] [Countable E]

omit [Countable E] in
lemma restrictedLayerCount_iUnion (I : ℕ → Set E) (hI : Monotone I)
    (A : Set V) (ω : Set E) (x : V) :
    restrictedLayerCount G (⋃ n, I n) A ω x = ⨆ n, restrictedLayerCount G (I n) A ω x := by
  let : MeasurableSpace V := ⊤
  let : MeasurableSingletonClass V := ⟨fun _ => trivial⟩
  let f (n : ℕ) (y : V) : ℝ≥0∞ := if y ∈ A ∧ Conn G (ω ∩ I n) x y then 1 else 0
  have hf : ∀ n, Measurable (f n) := fun _ => measurable_of_countable _
  have hmono : Monotone f := by
    intro n m hnm y
    by_cases hy : y ∈ A ∧ Conn G (ω ∩ I n) x y
    · have hym : y ∈ A ∧ Conn G (ω ∩ I m) x y :=
        ⟨hy.1,conn_mono G (inter_subset_inter_right ω (hI hnm)) hy.2⟩
      simp only [f,ite_eq_left hy,ite_eq_left hym,le_refl]
    · simp only [f,ite_eq_right hy]
      exact bot_le
  have hpoint (y : V) : (if y ∈ A ∧ Conn G (ω ∩ ⋃ n, I n) x y then (1 : ℝ≥0∞) else 0)=
      ⨆ n, f n y := by
    by_cases hy : y ∈ A ∧ Conn G (ω ∩ ⋃ n, I n) x y
    · rw [ite_eq_left hy]
      have he : ω ∩ ⋃ n, I n=⋃ n, ω ∩ I n := inter_iUnion ω I
      obtain ⟨n,hn⟩ := (conn_iUnion_iff G (fun n => ω ∩ I n)
        (fun _ _ h => inter_subset_inter_right ω (hI h)) x y).mp (he ▸ hy.2)
      apply le_antisymm
      · exact le_iSup_of_le n (by
          dsimp [f]
          rw [ite_eq_left (show y ∈ A ∧ Conn G (ω ∩ I n) x y from ⟨hy.1,hn⟩)])
      · exact iSup_le fun n => by dsimp [f]; split_ifs <;> simp
    · rw [ite_eq_right hy]
      apply le_antisymm bot_le
      apply iSup_le
      intro n
      have hn : ¬(y ∈ A ∧ Conn G (ω ∩ I n) x y) := fun hh =>
        hy ⟨hh.1,conn_mono G (inter_subset_inter_right ω (subset_iUnion I n)) hh.2⟩
      simp [f,hn]
  unfold restrictedLayerCount
  simp_rw [hpoint]
  rw [←lintegral_count (fun y => ⨆ n, f n y),lintegral_iSup hf hmono]
  simp_rw [lintegral_count]
  rfl

theorem restrictedLayerMoment_iUnion (I : ℕ → Set E) (hI : Monotone I)
    (A : Set V) (x : V) (p : unitInterval) {q : ℝ} (hq : 0 < q) :
    (∫⁻ ω, (restrictedLayerCount G (⋃ n, I n) A ω x)^q ∂law p)=
      ⨆ n, ∫⁻ ω, (restrictedLayerCount G (I n) A ω x)^q ∂law p := by
  have hp (ω : Set E) : (restrictedLayerCount G (⋃ n, I n) A ω x)^q =
      ⨆ n, (restrictedLayerCount G (I n) A ω x)^q := by
    rw [restrictedLayerCount_iUnion G I hI A ω x]
    exact (ENNReal.orderIsoRpow q hq).map_iSup _
  simp_rw [hp]
  apply lintegral_iSup
  · intro n
    exact (measurable_restrictedLayerCount G (I n) A x).pow_const q
  · intro n m hnm ω
    exact ENNReal.rpow_le_rpow (restrictedLayerCount_mono_edges G (hI hnm) A ω x) hq.le

end Percolation.BenjaminiSchramm

end

end OAI
