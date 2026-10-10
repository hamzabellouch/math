import OAI.Geometry.HeilbronnTriangle.ProportionalPairs
import OAI.Geometry.HeilbronnTriangle.CRTLifting

namespace OAI


open Finset

noncomputable section

namespace Problem355.LiftCollisions

abbrev Column := Fin 3 → ℤ

def InBox (N : ℕ) (u : Column) : Prop :=
  0 ≤ u 0 ∧ u 0 < N ∧ 0 ≤ u 1 ∧ u 1 < N ∧ (N : ℤ) ≤ u 2 ∧ u 2 < 2 * N

def natColumn (u : Column) : ProportionalPairs.NatColumn :=
  (((u 0).toNat, (u 1).toNat), (u 2).toNat)

def intColumn (u : ProportionalPairs.NatColumn) : Column :=
  ![(u.1.1 : ℤ), (u.1.2 : ℤ), (u.2 : ℤ)]

lemma nonneg_of_inBox {N : ℕ} {u : Column} (hu : InBox N u) : ∀ i, 0 ≤ u i := by
  intro i
  fin_cases i <;> dsimp <;> simp only [InBox] at hu <;> omega

lemma intColumn_natColumn {u : Column} (hu : ∀ i, 0 ≤ u i) :
    intColumn (natColumn u) = u := by
  funext i
  fin_cases i <;> simp [intColumn, natColumn, Int.toNat_of_nonneg (hu _)]

lemma natColumn_mem_box {N : ℕ} {u : Column} (hu : InBox N u) :
    natColumn u ∈ ProportionalPairs.columnBox N := by
  simp only [natColumn, ProportionalPairs.columnBox, mem_product, mem_range, mem_Ico]
  simp only [InBox] at hu
  omega

def project (u : Column) : ℝ × ℝ :=
  ((u 0 : ℝ) / (u 2 : ℝ), (u 1 : ℝ) / (u 2 : ℝ))

lemma project_intColumn (u : ProportionalPairs.NatColumn) :
    project (intColumn u) = ProportionalPairs.project u := by
  simp [project, intColumn, ProportionalPairs.project]

lemma project_natColumn {u : Column} (hu : ∀ i, 0 ≤ u i) :
    ProportionalPairs.project (natColumn u) = project u := by
  rw [← project_intColumn, intColumn_natColumn hu]

theorem card_equal_projection_pairs_le (N : ℕ) (hN : 0 < N)
    (U V : Finset Column) (hU : ∀ u ∈ U, InBox N u) (hV : ∀ v ∈ V, InBox N v) :
    ((U ×ˢ V).filter fun p => project p.1 = project p.2).card ≤ 8 * N ^ 3 := by
  classical
  let f : Column × Column → ProportionalPairs.NatColumn × ProportionalPairs.NatColumn :=
    fun p => (natColumn p.1, natColumn p.2)
  let T := ((ProportionalPairs.columnBox N ×ˢ ProportionalPairs.columnBox N).filter
    fun p => ProportionalPairs.project p.1 = ProportionalPairs.project p.2)
  let S := ((U ×ˢ V).filter fun p => project p.1 = project p.2)
  have hf : Set.MapsTo f ↑S ↑T := by
    intro p hp
    change p ∈ S at hp
    change f p ∈ T
    obtain ⟨hp, he⟩ := mem_filter.mp hp
    obtain ⟨hu, hv⟩ := mem_product.mp hp
    have hbu := hU p.1 hu
    have hbv := hV p.2 hv
    exact mem_filter.mpr ⟨mem_product.mpr ⟨natColumn_mem_box hbu, natColumn_mem_box hbv⟩,
      by simpa only [f, project_natColumn (nonneg_of_inBox hbu),
        project_natColumn (nonneg_of_inBox hbv)] using he⟩
  have hi : Set.InjOn f ↑S := by
    intro p hp q hq hpq
    change p ∈ S at hp
    change q ∈ S at hq
    have hp' := mem_product.mp (mem_filter.mp hp).1
    have hq' := mem_product.mp (mem_filter.mp hq).1
    have h1 := congrArg (fun z => intColumn z.1) hpq
    have h2 := congrArg (fun z => intColumn z.2) hpq
    simp only [f, intColumn_natColumn (nonneg_of_inBox (hU _ hp'.1)),
      intColumn_natColumn (nonneg_of_inBox (hU _ hq'.1))] at h1
    simp only [f, intColumn_natColumn (nonneg_of_inBox (hV _ hp'.2)),
      intColumn_natColumn (nonneg_of_inBox (hV _ hq'.2))] at h2
    exact Prod.ext h1 h2
  exact (card_le_card_of_injOn f hf hi).trans
    (ProportionalPairs.card_equal_projection_pairs_le N hN)

theorem uniform_collision_fraction_le (N Q L : ℕ) (hQ : 0 < Q) (hL : 0 < L)
    (hN : N = Q * L) (U V : Finset Column)
    (hU : ∀ u ∈ U, InBox N u) (hV : ∀ v ∈ V, InBox N v)
    (hUc : U.card = L ^ 3) (hVc : V.card = L ^ 3) :
    (((U ×ˢ V).filter fun p => project p.1 = project p.2).card : ℝ) /
        ((U.card : ℝ) * (V.card : ℝ)) ≤ 8 * (Q : ℝ) ^ 6 / (N : ℝ) ^ 3 := by
  classical
  have hNpos : 0 < N := by rw [hN]; positivity
  have hcount : (((U ×ˢ V).filter fun p => project p.1 = project p.2).card : ℝ) ≤
      8 * (N : ℝ) ^ 3 := by
    exact_mod_cast card_equal_projection_pairs_le N hNpos U V hU hV
  have hQr : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hLr : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  rw [hUc, hVc]
  push_cast
  calc
    _ ≤ (8 * (N : ℝ) ^ 3) / ((L : ℝ) ^ 3 * (L : ℝ) ^ 3) :=
      div_le_div_of_nonneg_right hcount (by positivity)
    _ = 8 * (Q : ℝ) ^ 6 / (N : ℝ) ^ 3 := by
      rw [hN]
      push_cast
      field_simp

def samplingShift (N : ℕ) : Fin 3 → ℤ := ![0, 0, (N : ℤ)]

def lifts (h q L : ℕ) (a b : Fin 3 → ℕ) : Finset Column :=
  CRT.integerColumnLifts h q L 3 a b (samplingShift (L * (h * q)))

lemma lifts_inBox (h q L : ℕ) (a b : Fin 3 → ℕ) (u : Column)
    (hu : u ∈ lifts h q L a b) : InBox (L * (h * q)) u := by
  have hv := (CRT.mem_integerColumnLifts_iff h q L 3 a b
    (samplingShift (L * (h * q))) u).mp hu
  have h0 := (hv 0).1
  have h1 := (hv 1).1
  have h2 := (hv 2).1
  simp [samplingShift] at h0 h1 h2
  dsimp [InBox]
  omega

lemma card_lifts (h q L : ℕ) (hh : 0 < h) (hq : 0 < q) (hc : h.Coprime q)
    (a b : Fin 3 → ℕ) (ha : ∀ i, a i < h) (hb : ∀ i, b i < q) :
    (lifts h q L a b).card = L ^ 3 := by
  apply CRT.card_integerColumnLifts h q L 3 hh hq hc a b ha hb
  · intro i
    fin_cases i <;> simp [samplingShift, Int.mul_emod]
  · intro i
    fin_cases i <;> simp [samplingShift, Int.mul_emod]

theorem crt_uniform_collision_fraction_le (h q L : ℕ)
    (hh : 0 < h) (hq : 0 < q) (hL : 0 < L) (hc : h.Coprime q)
    (a₁ b₁ a₂ b₂ : Fin 3 → ℕ)
    (ha₁ : ∀ i, a₁ i < h) (hb₁ : ∀ i, b₁ i < q)
    (ha₂ : ∀ i, a₂ i < h) (hb₂ : ∀ i, b₂ i < q) :
    (((lifts h q L a₁ b₁ ×ˢ lifts h q L a₂ b₂).filter
      fun p => project p.1 = project p.2).card : ℝ) /
        (((lifts h q L a₁ b₁).card : ℝ) * ((lifts h q L a₂ b₂).card : ℝ)) ≤
      8 * ((h * q : ℕ) : ℝ) ^ 6 / ((L * (h * q) : ℕ) : ℝ) ^ 3 := by
  apply uniform_collision_fraction_le _ (h * q) L (Nat.mul_pos hh hq) hL (Nat.mul_comm _ _)
  · exact lifts_inBox h q L a₁ b₁
  · exact lifts_inBox h q L a₂ b₂
  · exact card_lifts h q L hh hq hc a₁ b₁ ha₁ hb₁
  · exact card_lifts h q L hh hq hc a₂ b₂ ha₂ hb₂

end Problem355.LiftCollisions

end

end OAI
