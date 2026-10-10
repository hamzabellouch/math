import OAI.GroupTheory.Thompson.UniformPL
import OAI.GroupTheory.Thompson.AffineGridArithmetic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.Choose

namespace OAI

noncomputable section

namespace ThompsonNonamenability

open BasicPartition

/-- Every actual image of a depth-`n` uniform cell is a basic interval. -/
def ImageBasic (g : F) (n : ℕ) : Prop :=
  ∀ k : Fin (2 ^ n), ∃ I : BasicInterval,
    I.left = (g (uniformDyadicPoint n k.castSucc) : ℝ) ∧
    I.right = (g (uniformDyadicPoint n k.succ) : ℝ)

/-- The unique basic interval with the actual image endpoints. -/
def imageCell (g : F) (n : ℕ) (hg : ImageBasic g n) (k : Fin (2 ^ n)) :
    BasicInterval := Classical.choose (hg k)

@[simp] theorem imageCell_left (g : F) (n : ℕ) (hg : ImageBasic g n)
    (k : Fin (2 ^ n)) :
    (imageCell g n hg k).left = (g (uniformDyadicPoint n k.castSucc) : ℝ) :=
  (Classical.choose_spec (hg k)).1

@[simp] theorem imageCell_right (g : F) (n : ℕ) (hg : ImageBasic g n)
    (k : Fin (2 ^ n)) :
    (imageCell g n hg k).right = (g (uniformDyadicPoint n k.succ) : ℝ) :=
  (Classical.choose_spec (hg k)).2

theorem imageCell_proof_irrel (g : F) (n : ℕ) (hg hg' : ImageBasic g n)
    (k : Fin (2 ^ n)) : imageCell g n hg k = imageCell g n hg' k := by
  apply BasicInterval.ext_endpoints <;> simp

theorem imageCell_mem_carrier_iff (g : F) (n : ℕ) (hg : ImageBasic g n)
    (k : Fin (2 ^ n)) (x : UnitInterval) :
    (g x : ℝ) ∈ (imageCell g n hg k).carrier ↔
      (x : ℝ) ∈ (uniformCell n k).carrier := by
  simp only [BasicInterval.carrier, Set.mem_Icc, imageCell_left, imageCell_right]
  change g (uniformDyadicPoint n k.castSucc) ≤ g x ∧
      g x ≤ g (uniformDyadicPoint n k.succ) ↔ _
  rw [g.strictMono.le_iff_le, g.strictMono.le_iff_le]
  change (uniformDyadicPoint n k.castSucc : ℝ) ≤ (x : ℝ) ∧
      (x : ℝ) ≤ (uniformDyadicPoint n k.succ : ℝ) ↔ _
  rw [uniformDyadicPoint_castSucc_coe, uniformDyadicPoint_succ_coe]

theorem imageCell_mem_interior_iff (g : F) (n : ℕ) (hg : ImageBasic g n)
    (k : Fin (2 ^ n)) (x : UnitInterval) :
    (g x : ℝ) ∈ (imageCell g n hg k).interior ↔
      (x : ℝ) ∈ (uniformCell n k).interior := by
  simp only [BasicInterval.interior, Set.mem_Ioo, imageCell_left, imageCell_right]
  change g (uniformDyadicPoint n k.castSucc) < g x ∧
      g x < g (uniformDyadicPoint n k.succ) ↔ _
  rw [g.strictMono.lt_iff_lt, g.strictMono.lt_iff_lt]
  change (uniformDyadicPoint n k.castSucc : ℝ) < (x : ℝ) ∧
      (x : ℝ) < (uniformDyadicPoint n k.succ : ℝ) ↔ _
  rw [uniformDyadicPoint_castSucc_coe, uniformDyadicPoint_succ_coe]

theorem imageCell_injective (g : F) (n : ℕ) (hg : ImageBasic g n) :
    Function.Injective (imageCell g n hg) := by
  intro k l heq
  have hl : (g (uniformDyadicPoint n k.castSucc) : ℝ) =
      (g (uniformDyadicPoint n l.castSucc) : ℝ) := by
    simpa only [imageCell_left] using congrArg BasicInterval.left heq
  have hp := g.strictMono.injective (Subtype.ext hl)
  have hp' := congrArg (fun x : UnitInterval => (x : ℝ)) hp
  have hd : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  change (k.val : ℝ) / (2 : ℝ) ^ n = (l.val : ℝ) / (2 : ℝ) ^ n at hp'
  have hk : (k.val : ℝ) = (l.val : ℝ) := (div_left_inj' hd).mp hp'
  apply Fin.ext
  exact_mod_cast hk

/-- The actual images, with coverage and disjoint open interiors proved. -/
def imagePartition (g : F) (n : ℕ) (hg : ImageBasic g n) : BasicPartition where
  cells := Finset.univ.image (imageCell g n hg)
  cover := by
    intro x hx
    let y : UnitInterval := g.toHomeomorph.symm ⟨x, hx⟩
    have hgy : g y = (⟨x, hx⟩ : UnitInterval) :=
      g.toHomeomorph.apply_symm_apply ⟨x, hx⟩
    obtain ⟨I, hI, hyI⟩ := uniformCells_cover n (y : ℝ) y.property
    obtain ⟨k, rfl⟩ := mem_uniformCells.mp hI
    refine ⟨imageCell g n hg k, Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩, ?_⟩
    have hm := (imageCell_mem_carrier_iff g n hg k y).mpr hyI
    simpa only [hgy] using hm
  disjoint := by
    intro I hI J hJ hne
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hI
    obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hJ
    apply Set.disjoint_left.mpr
    intro x hxk hxl
    have hx : x ∈ Set.Icc (0 : ℝ) 1 :=
      (imageCell g n hg k).carrier_subset_unit
        ((imageCell g n hg k).interior_subset_carrier hxk)
    let y : UnitInterval := g.toHomeomorph.symm ⟨x, hx⟩
    have hgy : g y = (⟨x, hx⟩ : UnitInterval) :=
      g.toHomeomorph.apply_symm_apply ⟨x, hx⟩
    have hyk : (y : ℝ) ∈ (uniformCell n k).interior :=
      (imageCell_mem_interior_iff g n hg k y).mp (by simpa only [hgy] using hxk)
    have hyl : (y : ℝ) ∈ (uniformCell n l).interior :=
      (imageCell_mem_interior_iff g n hg l y).mp (by simpa only [hgy] using hxl)
    have hkl : k ≠ l := fun h => hne (congrArg (imageCell g n hg) h)
    exact Set.disjoint_left.mp (uniformCell_disjoint hkl) hyk hyl

@[simp] theorem imagePartition_cells (g : F) (n : ℕ) (hg : ImageBasic g n) :
    (imagePartition g n hg).cells = Finset.univ.image (imageCell g n hg) := rfl

@[simp] theorem mem_imagePartition_cells (g : F) (n : ℕ) (hg : ImageBasic g n)
    (I : BasicInterval) :
    I ∈ (imagePartition g n hg).cells ↔ ∃ k, imageCell g n hg k = I := by
  simp only [imagePartition_cells, Finset.mem_image, Finset.mem_univ, true_and]

theorem imagePartition_proof_irrel (g : F) (n : ℕ) (hg hg' : ImageBasic g n) :
    imagePartition g n hg = imagePartition g n hg' := by
  rfl

@[simp] theorem imagePartition_cellCount (g : F) (n : ℕ) (hg : ImageBasic g n) :
    (imagePartition g n hg).cellCount = 2 ^ n := by
  simp only [BasicPartition.cellCount, imagePartition_cells,
    Finset.card_image_of_injective _ (imageCell_injective g n hg), Finset.card_univ,
    Fintype.card_fin]

/-- Simultaneously gives actual image cells and the desired mesh bound. -/
theorem eventually_image_cells_small (g : F) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ k : Fin (2 ^ n), ∃ I : BasicInterval,
      I.left = (g (uniformDyadicPoint n k.castSucc) : ℝ) ∧
      I.right = (g (uniformDyadicPoint n k.succ) : ℝ) ∧ I.length < ε := by
  let w := g.witness
  let b : Fin w.pieceCount → ℝ := fun i =>
    (g (w.knots i.castSucc) : ℝ) -
      (2 : ℝ) ^ w.exponent i * (w.knots i.castSucc : ℝ)
  have hb : ∀ i, IsDyadic (b i) := by
    intro i
    exact (w.image_knots_dyadic g.strictMono i.castSucc).sub
      ((isDyadic_zpow (w.exponent i)).mul (w.dyadic i.castSucc))
  have halign := fun i => dyadic_affine_grid_alignment_small
    (w.exponent i) (b i) (hb i) ε hε
  choose Ns hNs using halign
  obtain ⟨Nr, hNr⟩ := w.eventually_uniform_refines
  refine ⟨max Nr (Finset.univ.sup Ns), ?_⟩
  intro n hn k
  obtain ⟨i, hil, hir⟩ := hNr n ((le_max_left _ _).trans hn) k
  have horder : uniformDyadicPoint n k.castSucc ≤ uniformDyadicPoint n k.succ := by
    change (uniformDyadicPoint n k.castSucc : ℝ) ≤ (uniformDyadicPoint n k.succ : ℝ)
    rw [uniformDyadicPoint_castSucc_coe, uniformDyadicPoint_succ_coe]
    exact (uniformCell n k).left_lt_right.le
  have hl := w.affine i (uniformDyadicPoint n k.castSucc) hil (horder.trans hir)
  have hr := w.affine i (uniformDyadicPoint n k.succ) (hil.trans horder) hir
  have hleft : (g (uniformDyadicPoint n k.castSucc) : ℝ) =
      (2 : ℝ) ^ w.exponent i * ((k.val : ℝ) / (2 : ℝ) ^ n) + b i := by
    change (g (uniformDyadicPoint n k.castSucc) : ℝ) = _ at hl
    rw [uniformDyadicPoint_castSucc_coe] at hl
    change (g (uniformDyadicPoint n k.castSucc) : ℝ) =
      (g (w.knots i.castSucc) : ℝ) +
        (2 : ℝ) ^ w.exponent i * ((k.val : ℝ) / (2 : ℝ) ^ n - _) at hl
    dsimp only [b]
    nlinarith [hl]
  have hright : (g (uniformDyadicPoint n k.succ) : ℝ) =
      (2 : ℝ) ^ w.exponent i * (((k.val : ℝ) + 1) / (2 : ℝ) ^ n) + b i := by
    change (g (uniformDyadicPoint n k.succ) : ℝ) = _ at hr
    rw [uniformDyadicPoint_succ_coe] at hr
    change (g (uniformDyadicPoint n k.succ) : ℝ) =
      (g (w.knots i.castSucc) : ℝ) +
        (2 : ℝ) ^ w.exponent i * (((k.val : ℝ) + 1) / (2 : ℝ) ^ n - _) at hr
    dsimp only [b]
    nlinarith [hr]
  have hNi : Ns i ≤ n :=
    (Finset.le_sup (Finset.mem_univ i)).trans ((le_max_right _ _).trans hn)
  obtain ⟨I, hIl, hIr, hIs⟩ := hNs i n hNi k
    (hleft ▸ (g (uniformDyadicPoint n k.castSucc)).property.1)
    (hright ▸ (g (uniformDyadicPoint n k.succ)).property.2)
  exact ⟨I, hIl.trans hleft.symm, hIr.trans hright.symm, hIs⟩

theorem eventually_image_basic (g : F) : ∃ N, ∀ n ≥ N, ImageBasic g n := by
  obtain ⟨N, hN⟩ := eventually_image_cells_small g 1 zero_lt_one
  refine ⟨N, ?_⟩
  intro n hn k
  obtain ⟨I, hl, hr, _⟩ := hN n hn k
  exact ⟨I, hl, hr⟩

theorem eventually_image_mesh_lt (g : F) (ε : ℝ) (hε : 0 < ε) :
    ∃ N, ∀ n ≥ N, ∃ hg : ImageBasic g n,
      ∀ I ∈ (imagePartition g n hg).cells, I.length < ε := by
  obtain ⟨N, hN⟩ := eventually_image_cells_small g ε hε
  refine ⟨N, ?_⟩
  intro n hn
  have hg : ImageBasic g n := by
    intro k
    obtain ⟨I, hl, hr, _⟩ := hN n hn k
    exact ⟨I, hl, hr⟩
  refine ⟨hg, ?_⟩
  intro I hI
  obtain ⟨k, rfl⟩ := (mem_imagePartition_cells g n hg I).mp hI
  obtain ⟨J, hl, hr, hJ⟩ := hN n hn k
  have heq : imageCell g n hg k = J :=
    BasicInterval.ext_endpoints ((imageCell_left g n hg k).trans hl.symm)
      ((imageCell_right g n hg k).trans hr.symm)
  simpa only [heq] using hJ

/-- A single actual grid level works for both finite families. -/
theorem eventually_image_respects (K : Finset F) (J : Finset BasicInterval) :
    ∃ N, ∀ n ≥ N, ∀ g ∈ K, ∃ hg : ImageBasic g n,
      ∀ I ∈ J, (imagePartition g n hg).Respects I := by
  classical
  have hsingle : ∀ g : F, ∃ N, ∀ n ≥ N, ∃ hg : ImageBasic g n,
      ∀ I ∈ J, (imagePartition g n hg).Respects I := by
    intro g
    induction J using Finset.induction_on with
    | empty =>
        obtain ⟨N, hN⟩ := eventually_image_basic g
        exact ⟨N, fun n hn => ⟨hN n hn, by simp⟩⟩
    | @insert I J hIJ ih =>
        obtain ⟨N₁, hN₁⟩ := ih
        obtain ⟨N₂, hN₂⟩ := eventually_image_mesh_lt g I.length I.length_pos
        refine ⟨max N₁ N₂, ?_⟩
        intro n hn
        obtain ⟨hg, hrest⟩ := hN₁ n ((le_max_left _ _).trans hn)
        obtain ⟨hg', hmesh⟩ := hN₂ n ((le_max_right _ _).trans hn)
        refine ⟨hg, ?_⟩
        intro L hL
        rcases Finset.mem_insert.mp hL with hLI | hL
        · subst L
          exact (imagePartition g n hg).respects_of_mesh_lt I hmesh
        · exact hrest L hL
  choose Ns hNs using hsingle
  refine ⟨K.sup Ns, ?_⟩
  intro n hn g hg
  exact hNs g n ((Finset.le_sup hg).trans hn)

end ThompsonNonamenability

end

end OAI
