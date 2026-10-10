import OAI.Probability.RadialTransition.PairEnsembles

namespace OAI

universe uG

noncomputable section


open Function MeasureTheory Set Filter

open scoped ContDiff NNReal BigOperators ENNReal

namespace RadialTransition

theorem pairGrand_grid_perturbation {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (e : I → Cell) (he : Function.Injective e) {A : Set Position}
    (hA : MeasurableSet A) (hcover : ∀ x ∈ A, ∃ i, cellOf x = e i)
    (v w : Position → Position → ℝ)
    (hv : Measurable (Function.uncurry v)) (hw : Measurable (Function.uncurry w))
    (hvcell : ∀ i j, Continuous (fun p : CroppedCell A (e i) × CroppedCell A (e j) => v p.1 p.2))
    (hwcell : ∀ i j, Continuous (fun p : CroppedCell A (e i) × CroppedCell A (e j) => w p.1 p.2))
    (hvsym : ∀ x y, v x y = v y x) (hwsym : ∀ x y, w x y = w y x)
    {t β : ℝ} (ht : 0 < t) (hβ : 0 < β) (z : ℝ)
    (J K : Cell → Cell → ℝ)
    (hJ : ∀ i j, 0 ≤ J i j) (hJsym : ∀ i j, J i j = J j i)
    (hrow : ∀ i, ∑ j, J (e i) (e j) ≤ (t^2/8)/8)
    (hintrav : ∀ x y, cellOf x = cellOf y → corePotential t (nndist x y)-J (cellOf x) (cellOf y) ≤ v x y)
    (hcrossv : ∀ x y, -J (cellOf x) (cellOf y) ≤ v x y)
    (hintraw : ∀ x y, cellOf x = cellOf y → corePotential t (nndist x y)-J (cellOf x) (cellOf y) ≤ w x y)
    (hcrossw : ∀ x y, -J (cellOf x) (cellOf y) ≤ w x y)
    (hK : ∀ i j, 0 ≤ K i j)
    (hd : ∀ x y, |w x y-v x y| ≤ K (cellOf x) (cellOf y)) :
    |Real.log (pairGrand v (volume.restrict A) β z)-Real.log (pairGrand w (volume.restrict A) β z)| ≤
      β/2 * localMomentBound t β z * ∑ i, ∑ j, K (e i) (e j) := by
  let X i := CroppedCell A (e i)
  let ν i := croppedCellMeasure A (e i)
  let : ∀ i, IsFiniteMeasure (ν i) := fun i => croppedCellMeasure_finite hA (e i)
  let pos : ∀ i, X i → Position := fun _ => Subtype.val
  have hpos (i : I) : Measurable (pos i) := measurable_subtype_coe
  have hcell (i : I) (x : X i) : cellOf (pos i x) = e i := x.property.2
  have heqv := pairGrand_eq_cell X ν pos hpos v hv hvsym (croppedCell_partition e he hA hcover) β z
  have heqw := pairGrand_eq_cell X ν pos hpos w hw hwsym (croppedCell_partition e he hA hcover) β z
  rw [heqv, heqw]
  apply pairCell_log_perturbation ν pos (fun i => croppedCell_diameter) ht hβ (by norm_num)
    (fun i => croppedCellMeasure_volume hA (e i))
    (fun i j x y => v (pos i x) (pos j y)) (fun i j x y => w (pos i x) (pos j y))
    hvcell hwcell (fun i j x y => hvsym _ _) (fun i j x y => hwsym _ _)
    (fun i j => J (e i) (e j)) (fun i j => hJ _ _) (fun i j => hJsym _ _) hrow
  · intro i x y
    simpa only [hcell] using hintrav (pos i x) (pos i y) ((hcell i x).trans (hcell i y).symm)
  · intro i j x y
    simpa only [hcell] using hcrossv (pos i x) (pos j y)
  · intro i x y
    simpa only [hcell] using hintraw (pos i x) (pos i y) ((hcell i x).trans (hcell i y).symm)
  · intro i j x y
    simpa only [hcell] using hcrossw (pos i x) (pos j y)
  · exact fun i j => hK _ _
  · intro i j x y
    simpa only [hcell] using hd (pos i x) (pos j y)

def deletedPair {G : Type uG} [DecidableEq G] (g : Cell → G) (φ χ : Potential)
    (x y : Position) : ℝ :=
  (if g (cellOf x) = g (cellOf y) then radialPair φ x y else 0) + radialPair χ x y

lemma measurable_deletedPair {G : Type uG} [DecidableEq G] (g : Cell → G)
    {φ χ : Potential} (hφ : Continuous φ) (hχ : Continuous χ) :
    Measurable (Function.uncurry (deletedPair g φ χ)) := by
  have hp : MeasurableSet {p : Position × Position | g (cellOf p.1) = g (cellOf p.2)} := by
    have hh : MeasurableSet {p : Cell × Cell | g p.1 = g p.2} := Set.to_countable _ |>.measurableSet
    exact hh.preimage ((measurable_cellOf.comp measurable_fst).prodMk (measurable_cellOf.comp measurable_snd))
  exact ((continuous_radialPair hφ).measurable.ite hp measurable_const).add
    (continuous_radialPair hχ).measurable

lemma deletedPair_symm {G : Type uG} [DecidableEq G] (g : Cell → G) (φ χ : Potential) (x y : Position) :
    deletedPair g φ χ x y = deletedPair g φ χ y x := by
  simp only [deletedPair, show (g (cellOf y) = g (cellOf x)) = (g (cellOf x) = g (cellOf y)) from propext eq_comm, radialPair_symm φ y x, radialPair_symm χ y x]

lemma continuous_deletedPair_cell {G : Type uG} [DecidableEq G] (g : Cell → G)
    {φ χ : Potential} (hφ : Continuous φ) (hχ : Continuous χ)
    (A : Set Position) (i j : Cell) :
    Continuous (fun p : CroppedCell A i × CroppedCell A j => deletedPair g φ χ p.1 p.2) := by
  have he : (fun p : CroppedCell A i × CroppedCell A j => deletedPair g φ χ p.1 p.2) =
      (fun p => (if g i = g j then radialPair φ p.1 p.2 else 0)+radialPair χ p.1 p.2) := by
    funext p
    have h₁ : cellOf (p.1 : Position) = i := p.1.property.2
    have h₂ : cellOf (p.2 : Position) = j := p.2.property.2
    simp only [deletedPair, h₁, h₂]
  rw [he]
  apply Continuous.add
  · split_ifs
    · exact continuous_radialPair_comp hφ continuous_subtype_val continuous_subtype_val
    · exact continuous_const
  · exact continuous_radialPair_comp hχ continuous_subtype_val continuous_subtype_val

def deletionMajorant {G : Type uG} [DecidableEq G] (g : Cell → G) (W : Cell → Cell → ℝ)
    (i j : Cell) : ℝ := if g i = g j then 0 else W i j

lemma deletionMajorant_nonneg {G : Type uG} [DecidableEq G] (g : Cell → G)
    {W : Cell → Cell → ℝ} (hW : ∀ i j, 0 ≤ W i j) (i j : Cell) :
    0 ≤ deletionMajorant g W i j := ite_nonneg le_rfl (hW i j)

theorem deletedPair_grid_bound {I G : Type} [Fintype I] [DecidableEq I] [Nonempty I] [DecidableEq G]
    (e : I → Cell) (he : Function.Injective e) (g : Cell → G) {A : Set Position}
    (hA : MeasurableSet A) (hcover : ∀ x ∈ A, ∃ i, cellOf x = e i)
    {φ χ : Potential} (hφ : Continuous φ) (hχ : Continuous χ)
    {t β : ℝ} (ht : 0 < t) (hβ : 0 < β) (z : ℝ)
    (J₀ J₁ W : Cell → Cell → ℝ)
    (hJ₀ : ∀ i j, 0 ≤ J₀ i j) (hJ₁ : ∀ i j, 0 ≤ J₁ i j)
    (hJsym : ∀ i j, J₀ i j + J₁ i j = J₀ j i + J₁ j i)
    (hrow : ∀ i, ∑ j, (J₀ (e i) (e j)+J₁ (e i) (e j)) ≤ (t^2/8)/8)
    (hlφ : ∀ x y, corePotential t (nndist x y)-J₀ (cellOf x) (cellOf y) ≤ radialPair φ x y)
    (hlχ : ∀ x y, -J₁ (cellOf x) (cellOf y) ≤ radialPair χ x y)
    (hW : ∀ i j, 0 ≤ W i j) (hbφ : ∀ x y, |radialPair φ x y| ≤ W (cellOf x) (cellOf y)) :
    |Real.log (pairGrand (radialPair (φ+χ)) (volume.restrict A) β z)-
      Real.log (pairGrand (deletedPair g φ χ) (volume.restrict A) β z)| ≤
      β/2 * localMomentBound t β z * ∑ i, ∑ j, deletionMajorant g W (e i) (e j) := by
  have hcore (x y : Position) : 0 ≤ corePotential t (nndist x y) := coreReal_nonneg _ _
  have hall (x y : Position) : corePotential t (nndist x y)-(J₀ (cellOf x) (cellOf y)+J₁ (cellOf x) (cellOf y)) ≤
      radialPair (φ+χ) x y := by
    change _ ≤ radialPair φ x y+radialPair χ x y
    linarith [hlφ x y, hlχ x y]
  have hd (x y : Position) : |deletedPair g φ χ x y-radialPair (φ+χ) x y| ≤
      deletionMajorant g W (cellOf x) (cellOf y) := by
    unfold deletedPair deletionMajorant
    change |(if _ then _ else _)+radialPair χ x y-(radialPair φ x y+radialPair χ x y)| ≤ _
    split_ifs with h
    · simp only [sub_self, abs_zero, le_refl]
    · rw [show (0:ℝ)+radialPair χ x y-(radialPair φ x y+radialPair χ x y) = -radialPair φ x y by ring, abs_neg]
      exact hbφ x y
  apply pairGrand_grid_perturbation e he hA hcover (radialPair (φ+χ)) (deletedPair g φ χ)
    (continuous_radialPair (hφ.add hχ)).measurable (measurable_deletedPair g hφ hχ)
    (fun i j => continuous_radialPair_comp (hφ.add hχ) continuous_subtype_val continuous_subtype_val)
    (fun i j => continuous_deletedPair_cell g hφ hχ A (e i) (e j))
    (radialPair_symm _) (deletedPair_symm g φ χ) ht hβ z
    (fun i j => J₀ i j+J₁ i j) (deletionMajorant g W)
    (fun i j => add_nonneg (hJ₀ i j) (hJ₁ i j)) hJsym hrow
  · exact fun x y _ => hall x y
  · intro x y; linarith [hall x y, hcore x y]
  · intro x y heq
    change _ ≤ (if g (cellOf x) = g (cellOf y) then radialPair φ x y else 0)+radialPair χ x y
    rw [ite_eq_left (congrArg g heq)]
    exact hall x y
  · intro x y
    unfold deletedPair
    split_ifs
    · linarith [hlφ x y, hlχ x y, hcore x y]
    · linarith [hlχ x y, hJ₀ (cellOf x) (cellOf y)]
  · exact deletionMajorant_nonneg g hW
  · exact hd

end RadialTransition

end

end OAI
