import OAI.Probability.RadialTransition.CellDifferences

namespace OAI

noncomputable section


open Function MeasureTheory Set Filter

open scoped ContDiff NNReal BigOperators ENNReal

namespace RadialTransition

theorem grandOn_grid_perturbation {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (e : I → Cell) (he : Function.Injective e) {A : Set Position}
    (hA : MeasurableSet A) (hAfin : volume A ≠ ⊤)
    (hcover : ∀ x ∈ A, ∃ i, cellOf x = e i)
    {φ ψ : Potential} (hφ : Continuous φ) (hψ : Continuous ψ)
    (hbφ : IsBoundedPotential φ) (hbψ : IsBoundedPotential ψ)
    {Bφ Bψ t β : ℝ} (hsφ : StableWith φ Bφ) (hsψ : StableWith ψ Bψ)
    (ht : 0 < t) (hβ : 0 < β) (z : ℝ)
    (J K : Cell → Cell → ℝ)
    (hJ : ∀ i j, 0 ≤ J i j) (hJsym : ∀ i j, J i j = J j i)
    (hrow : ∀ i, ∑ j, J (e i) (e j) ≤ (t^2/8)/8)
    (hlφ : ∀ x y, corePotential t (nndist x y)-J (cellOf x) (cellOf y) ≤ φ (nndist x y))
    (hlψ : ∀ x y, corePotential t (nndist x y)-J (cellOf x) (cellOf y) ≤ ψ (nndist x y))
    (hK : ∀ i j, 0 ≤ K i j)
    (hd : ∀ x y, |ψ (nndist x y)-φ (nndist x y)| ≤ K (cellOf x) (cellOf y)) :
    |Real.log (grandOn φ A β z)-Real.log (grandOn ψ A β z)| ≤
      β/2 * (Real.exp (16/15 * (1/64) * Real.exp (z+β*(t^2/2))) / (β*(t^2/8)/4)) *
        ∑ i, ∑ j, K (e i) (e j) := by
  let X i := CroppedCell A (e i)
  let ν i := croppedCellMeasure A (e i)
  let : ∀ i, IsFiniteMeasure (ν i) := fun i => croppedCellMeasure_finite hA (e i)
  let pos : ∀ i, X i → Position := fun _ => Subtype.val
  have hpos (i : I) : Continuous (pos i) := continuous_subtype_val
  let v : ∀ i j, X i → X j → ℝ := fun i j x y => radialPair φ (pos i x) (pos j y)
  let w : ∀ i j, X i → X j → ℝ := fun i j x y => radialPair ψ (pos i x) (pos j y)
  have hcell (i : I) (x : X i) : cellOf (pos i x) = e i := x.property.2
  have hdecomp := croppedCell_partition e he hA hcover
  have heφ := (grandOn_cell_factorization X ν pos hpos hAfin hdecomp hφ hbφ hsφ hβ.le z).2
  have heψ := (grandOn_cell_factorization X ν pos hpos hAfin hdecomp hψ hbψ hsψ hβ.le z).2
  rw [← heφ, ← heψ]
  have hv (i j : I) : Continuous (Function.uncurry (v i j)) := by
    change Continuous (fun p : X i × X j => radialPair φ (pos i p.1) (pos j p.2))
    exact continuous_radialPair_comp hφ (hpos i) (hpos j)
  have hw (i j : I) : Continuous (Function.uncurry (w i j)) := by
    change Continuous (fun p : X i × X j => radialPair ψ (pos i p.1) (pos j p.2))
    exact continuous_radialPair_comp hψ (hpos i) (hpos j)
  have hlowφ (i j : I) (x : X i) (y : X j) :
      corePotential t (nndist (pos i x) (pos j y))-J (e i) (e j) ≤ v i j x y := by
    simpa only [hcell, v, radialPair] using hlφ (pos i x) (pos j y)
  have hlowψ (i j : I) (x : X i) (y : X j) :
      corePotential t (nndist (pos i x) (pos j y))-J (e i) (e j) ≤ w i j x y := by
    simpa only [hcell, w, radialPair] using hlψ (pos i x) (pos j y)
  exact pairCell_log_perturbation ν pos (fun i => croppedCell_diameter) ht hβ (by norm_num)
    (fun i => croppedCellMeasure_volume hA (e i)) v w hv hw
    (fun i j x y => radialPair_symm φ _ _) (fun i j x y => radialPair_symm ψ _ _)
    (fun i j => J (e i) (e j)) (fun i j => hJ _ _) (fun i j => hJsym _ _) hrow
    (fun i => hlowφ i i)
    (fun i j x y => (by have hh := hlowφ i j x y; have hn := coreReal_nonneg t (nndist (pos i x) (pos j y)); change 0 ≤ corePotential t (nndist (pos i x) (pos j y)) at hn; linarith))
    (fun i => hlowψ i i)
    (fun i j x y => (by have hh := hlowψ i j x y; have hn := coreReal_nonneg t (nndist (pos i x) (pos j y)); change 0 ≤ corePotential t (nndist (pos i x) (pos j y)) at hn; linarith))
    (fun i j => K (e i) (e j)) (fun i j => hK _ _)
    (fun i j x y => by simpa only [hcell, v, w, radialPair] using hd (pos i x) (pos j y))

lemma attractionProfile_mono {a b R : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n) (hR : ∀ n, 1 ≤ R n)
    (hsa : Summable a) (hsb : Summable b) (hab : ∀ n, a n ≤ b n) (r : ℝ) :
    attractionProfile a R r ≤ attractionProfile b R r :=
  Summable.tsum_le_tsum
    (fun n => mul_le_mul_of_nonneg_right (hab n) (scaledBumpProfile_nonneg (by linarith [hR n]) r))
    (summable_attractionProfile ha hR hsa r) (summable_attractionProfile hb hR hsb r)

lemma familyPotential_grid_lower {t : ℝ} {a m R : ℕ → ℝ} (ht : 0 ≤ t)
    (ha : ∀ n, 0 ≤ a n) (hm : ∀ n, 0 ≤ m n) (hR : ∀ n, 1 ≤ R n)
    (hsa : Summable a) (hsm : Summable m) (ham : ∀ n, a n ≤ m n) (x y : Position) :
    corePotential t (nndist x y)-familyCellMajorant t m R (cellOf x) (cellOf y) ≤
      familyPotential t a R (nndist x y) := by
  have hh := (mul_le_mul_of_nonneg_left (attractionProfile_mono ha hm hR hsa hsm ham (dist x y)) ht).trans
    (attraction_le_familyCellMajorant ht hm hR hsm x y)
  change coreReal t (dist x y)-_ ≤ coreReal t (dist x y)-t*attractionProfile a R (dist x y)
  linarith

lemma familyPotential_grid_difference {t : ℝ} {a b R : ℕ → ℝ} (ht : 0 ≤ t)
    (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n) (hR : ∀ n, 1 ≤ R n)
    (hsa : Summable a) (hsb : Summable b) (x y : Position) :
    |familyPotential t b R (nndist x y)-familyPotential t a R (nndist x y)| ≤
      familyCellMajorant t (fun n => |b n-a n|) R (cellOf x) (cellOf y) := by
  have hsd : Summable (fun n => |b n-a n|) := (hsb.sub hsa).abs
  have he : |attractionProfile b R (dist x y)-attractionProfile a R (dist x y)| ≤
      attractionProfile (fun n => |b n-a n|) R (dist x y) := by
    unfold attractionProfile
    rw [← (summable_attractionProfile hb hR hsb _).tsum_sub (summable_attractionProfile ha hR hsa _)]
    have hsn := ((summable_attractionProfile hb hR hsb (dist x y)).sub (summable_attractionProfile ha hR hsa (dist x y))).norm
    have hh := norm_tsum_le_tsum_norm hsn
    simp only [Real.norm_eq_abs, ← sub_mul, abs_mul] at hh
    have hn (n : ℕ) : |scaledBumpProfile (R n) (dist x y)| = scaledBumpProfile (R n) (dist x y) :=
      abs_of_nonneg (scaledBumpProfile_nonneg (by linarith [hR n]) _)
    simpa only [hn, ← sub_mul] using hh
  have hh := (mul_le_mul_of_nonneg_left he ht).trans
    (attraction_le_familyCellMajorant ht (fun n => abs_nonneg _) hR hsd x y)
  have heq : |familyPotential t b R (nndist x y)-familyPotential t a R (nndist x y)| =
      t*|attractionProfile b R (dist x y)-attractionProfile a R (dist x y)| := by
    change |(coreReal t (dist x y)-t*attractionProfile b R (dist x y))-
        (coreReal t (dist x y)-t*attractionProfile a R (dist x y))| = _
    rw [show (coreReal t (dist x y)-t*attractionProfile b R (dist x y))-
      (coreReal t (dist x y)-t*attractionProfile a R (dist x y)) =
      -(t*(attractionProfile b R (dist x y)-attractionProfile a R (dist x y))) by ring,
      abs_neg, abs_mul, abs_of_nonneg ht]
  rw [heq]
  exact hh

def localMomentBound (t β z : ℝ) : ℝ :=
  Real.exp (16/15*(1/64)*Real.exp (z+β*(t^2/2))) / (β*(t^2/8)/4)

def familyPressureLipschitz (t β h : ℝ) : ℝ :=
  216*(β/2*localMomentBound t β (t*h))*2197*bumpIntegral⁻¹

lemma localMomentBound_nonneg {t β : ℝ} (hβ : 0 ≤ β) (z : ℝ) :
    0 ≤ localMomentBound t β z := by unfold localMomentBound; positivity

lemma familyPressureLipschitz_nonneg {t β h : ℝ} (hβ : 0 ≤ β) :
    0 ≤ familyPressureLipschitz t β h := by
  unfold familyPressureLipschitz
  have hC := localMomentBound_nonneg (t := t) hβ (t*h)
  exact mul_nonneg (by positivity) (inv_nonneg.mpr bumpIntegral_pos.le)

theorem finiteGrandPressure_family_difference {t L β h : ℝ} {a b m R : ℕ → ℝ}
    (ht : 1 ≤ t) (hL : 1 ≤ L) (hβ : 0 < β)
    (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n) (hm : ∀ n, 0 ≤ m n)
    (hR : ∀ n, 1 ≤ R n) (hsa : Summable a) (hsb : Summable b) (hsm : Summable m)
    (ham : ∀ n, a n ≤ m n) (hbm : ∀ n, b n ≤ m n)
    (hrow : 2197*t*bumpIntegral⁻¹*(∑' n, m n) ≤ (t^2/8)/8) :
    |finiteGrandPressure (familyPotential t a R) t L β h-
      finiteGrandPressure (familyPotential t b R) t L β h| ≤
      familyPressureLipschitz t β h * ∑' n, |b n-a n| := by
  classical
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hcoeff : 0 ≤ 2197*t*bumpIntegral⁻¹ := mul_nonneg (by positivity) (inv_nonneg.mpr bumpIntegral_pos.le)
  have hstable (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (hsc : Summable c) (hcm : ∀ n, c n ≤ m n) :
      StableWith (familyPotential t c R) (t^2/2) := by
    apply stable_familyPotential ht0.le hc hR hsc
    have hh := (mul_le_mul_of_nonneg_left (hsc.tsum_le_tsum hcm hsm) hcoeff).trans hrow
    nlinarith [sq_nonneg t]
  let I := {k // k ∈ cubeCells L}
  let e : I → Cell := Subtype.val
  have he : Function.Injective e := Subtype.val_injective
  let : Nonempty I := ⟨⟨cellOf 0, cellOf_mem_cubeCells (by intro i; simp only [PiLp.zero_apply]; exact ⟨le_rfl, hL0.le⟩)⟩⟩
  let d n := |b n-a n|
  have hd : Summable d := (hsb.sub hsa).abs
  have hjrow (i : I) : ∑ j, familyCellMajorant t m R (e i) (e j) ≤ (t^2/8)/8 :=
    (familyCellMajorant_row e he ht0.le hm hR hsm (e i)).trans hrow
  have hh := grandOn_grid_perturbation e he (measurableSet_cube L)
    (by rw [volume_cube]; exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
    (fun x hx => ⟨⟨cellOf x, cellOf_mem_cubeCells hx⟩, rfl⟩)
    (continuous_familyPotential ha hR hsa t) (continuous_familyPotential hb hR hsb t)
    (bounded_familyPotential ha hR hsa t) (bounded_familyPotential hb hR hsb t)
    (hstable a ha hsa ham) (hstable b hb hsb hbm) ht0 hβ (t*h)
    (familyCellMajorant t m R) (familyCellMajorant t d R)
    (familyCellMajorant_nonneg ht0.le hm hR) (familyCellMajorant_symm t m R) hjrow
    (familyPotential_grid_lower ht0.le ha hm hR hsa hsm ham)
    (familyPotential_grid_lower ht0.le hb hm hR hsb hsm hbm)
    (familyCellMajorant_nonneg ht0.le (fun n => abs_nonneg _) hR)
    (familyPotential_grid_difference ht0.le ha hb hR hsa hsb)
  have hsum : (∑ i : I, ∑ j : I, familyCellMajorant t d R (e i) (e j)) ≤
      216*L^3*(2197*t*bumpIntegral⁻¹*∑' n, d n) := by
    calc
      _ ≤ ∑ i : I, (2197*t*bumpIntegral⁻¹*∑' n, d n) :=
        Finset.sum_le_sum (fun i _ => familyCellMajorant_row e he ht0.le (fun n => abs_nonneg _) hR hd (e i))
      _ = (Fintype.card I : ℝ)*(2197*t*bumpIntegral⁻¹*∑' n, d n) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by simpa only [I, Fintype.card_coe] using card_cubeCells hL)
        (mul_nonneg hcoeff (tsum_nonneg (fun n => abs_nonneg _)))
  change |Real.log (grandOn (familyPotential t a R) (cube L) β (t*h))-
      Real.log (grandOn (familyPotential t b R) (cube L) β (t*h))| ≤
      β/2*localMomentBound t β (t*h)*_ at hh
  rw [grandOn_cube, grandOn_cube] at hh
  unfold finiteGrandPressure
  rw [← sub_div, abs_div, abs_of_pos (mul_pos ht0 (pow_pos hL0 3))]
  apply (div_le_iff₀ (mul_pos ht0 (pow_pos hL0 3))).mpr
  calc
    _ ≤ β/2*localMomentBound t β (t*h)*(216*L^3*(2197*t*bumpIntegral⁻¹*∑' n, d n)) :=
      hh.trans (mul_le_mul_of_nonneg_left hsum (mul_nonneg (by positivity) (localMomentBound_nonneg hβ.le _)))
    _ = _ := by unfold familyPressureLipschitz; dsimp only [d]; ring

lemma stable_family_of_master {t : ℝ} {a m R : ℕ → ℝ} (ht : 0 ≤ t)
    (ha : ∀ n, 0 ≤ a n) (hR : ∀ n, 1 ≤ R n) (hsa : Summable a) (hsm : Summable m)
    (ham : ∀ n, a n ≤ m n)
    (hrow : 2197*t*bumpIntegral⁻¹*(∑' n, m n) ≤ (t^2/8)/8) :
    StableWith (familyPotential t a R) (t^2/2) := by
  apply stable_familyPotential ht ha hR hsa
  have hcoeff : 0 ≤ 2197*t*bumpIntegral⁻¹ := mul_nonneg (by positivity) (inv_nonneg.mpr bumpIntegral_pos.le)
  have hh := (mul_le_mul_of_nonneg_left (hsa.tsum_le_tsum ham hsm) hcoeff).trans hrow
  nlinarith [sq_nonneg t]

theorem grandPressure_family_difference {t β h : ℝ} {a b m R : ℕ → ℝ}
    (ht : 1 ≤ t) (hβ : 0 < β)
    (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n) (hm : ∀ n, 0 ≤ m n)
    (hR : ∀ n, 1 ≤ R n) (hsa : Summable a) (hsb : Summable b) (hsm : Summable m)
    (ham : ∀ n, a n ≤ m n) (hbm : ∀ n, b n ≤ m n)
    (hrow : 2197*t*bumpIntegral⁻¹*(∑' n, m n) ≤ (t^2/8)/8) :
    |grandPressure (familyPotential t a R) t β h-grandPressure (familyPotential t b R) t β h| ≤
      familyPressureLipschitz t β h * ∑' n, |b n-a n| := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hlim (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (hsc : Summable c) (hcm : ∀ n, c n ≤ m n) :
      Tendsto (fun L : ℝ => finiteGrandPressure (familyPotential t c R) t L β h) atTop
        (nhds (grandPressure (familyPotential t c R) t β h)) :=
    (grandPressure_spec (continuous_familyPotential hc hR hsc t) (bounded_familyPotential hc hR hsc t)
      (stable_family_of_master ht0.le hc hR hsc hsm hcm hrow) ht0 hβ.le
      (fun r hr => familyPotential_nonpos_outer hc hR ht hr) h).1
  apply le_of_tendsto ((hlim a ha hsa ham).sub (hlim b hb hsb hbm)).abs
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL
  exact finiteGrandPressure_family_difference ht hL hβ ha hb hm hR hsa hsb hsm ham hbm hrow

end RadialTransition

end

end OAI
