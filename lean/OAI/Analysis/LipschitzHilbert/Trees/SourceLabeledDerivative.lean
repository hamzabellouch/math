import OAI.Analysis.LipschitzHilbert.Trees.SourceSlottedConcentration
import OAI.Analysis.LipschitzHilbert.Trees.SourceCrossDerivative

namespace OAI

/-! The horizontal interval derivative bound for the original labeled
source collection. Actual physical analyzing coefficients are retained;
the fixed number of lattice slots costs one power of the large parameter. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert.SourceLabeledLattice

theorem planarPacketInterval_horizontal_differentiable_schwartz
    {N : ℕ} {κ : Type} {ι : Fin N → Type} [Fintype κ] [∀ j, Fintype (ι j)]
    (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (wave : ∀ j, ι j → κ → ℝ → SchwartzMap ℝ ℂ)
    (lower upper : ℕ) (hlu : lower ≤ upper) (x y : ℝ) :
    DifferentiableAt ℝ (fun x => planarPacketInterval coeff
      (fun j u k t s => wave j u k t s) lower upper x y) x := by
  have heq : (fun x => planarPacketInterval coeff (fun j u k t s => wave j u k t s)
      lower upper x y) = fun x =>
      ∑ j ∈ Finset.univ.filter (fun j : Fin N => lower ≤ j.val ∧ j.val < upper),
        vectorPacketSynthesis (coeff j) (fun u k => wave j u k y) x := by
    funext x
    exact planarPacketInterval_eq_selected coeff wave lower upper hlu x y
  rw [heq]
  exact DifferentiableAt.fun_sum (fun j _ =>
    (vectorPacketSynthesis_hasDerivAt (coeff j) (fun u k => wave j u k y) x).differentiableAt)

theorem lattice_rawInterval_horizontal_differentiable
    {N : ℕ} {κ : Type} {ι : Fin N → Type} [Fintype κ] [∀ j, Fintype (ι j)]
    (P : SourceLatticePacket N κ ι) (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (i : Fin 3) (lower upper : ℕ) (hlu : lower ≤ upper) (x y : ℝ) :
    DifferentiableAt ℝ (fun x => P.rawInterval coeff i lower upper x y) x := by
  exact planarPacketInterval_horizontal_differentiable_schwartz
    coeff (fun j u k t => P.raw i j u k t) lower upper hlu x y

theorem source_labeled_top_derivative (p : ℝ) (D B : ℕ) :
    ∃ L0 : ℝ, 1 ≤ L0 ∧ (B : ℝ) ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L →
      ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
        [Fintype κ] [∀ j l, Fintype (Item j l)]
        (P : SourceLabeledLattice N κ Label Item)
        (_hcard : ∀ j, (P.labels j).card ≤ B), P.constant ≤ L ^ p →
      ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ × ℝ) ℂ)
        (hAlt : ∀ j l u k,
          planarProfileConstant (alt j l u k) (2 * P.order) ≤ P.profileBound)
        (T : SlopeBox) (K : ℝ), 0 < K → SourceLabeledTopGeometry P T K D →
      ∀ (cutoff : Fin N → ℝ) (v : ℝ × ℝ → ℝ), Measurable v →
      ∀ (g : ℝ × ℝ → EuclideanSpace ℂ κ), Measurable g → (∀ z, ‖g z‖ ≤ 1) →
      ∀ (lower upper : ℕ), lower ≤ upper → ∀ r : ℝ, 0 < r →
      (∀ j : Fin N, lower ≤ j.val → j.val < upper → r ≤ P.length j) →
      ∀ z : ℝ × ℝ,
      ‖deriv (fun x => (P.withProfile alt hAlt).rawInterval
        (P.physicalCoefficient T.slope cutoff v g) 0 lower upper x (z.2 - T.slope * z.1)) z.1‖ ≤
          (L ^ (2 * p + 4) / r) * (T.weight K (D : ℝ) z) ^ 8 := by
  classical
  obtain ⟨L1, hL1, hderivative⟩ := SourceLatticePacket.source_cross_top_derivative p D
  refine ⟨max L1 B, hL1.trans (le_max_left _ _), le_max_right _ _, ?_⟩
  intro L hLL N κ Label Item _ _ P hcard hP alt hAlt T K hK G cutoff v hv g hg hg1
    lower upper hlu r hr hs z
  have hLpos : 0 < L := zero_lt_one.trans_le (hL1.trans ((le_max_left _ _).trans hLL))
  have hBL : (B : ℝ) ≤ L := (le_max_right _ _).trans hLL
  let Q := P.withProfile alt hAlt
  let coeff := P.physicalCoefficient T.slope cutoff v g
  let y := z.2 - T.slope * z.1
  let F := fun b : Fin B =>
    ((P.slotted hcard b).withProfile (P.slottedAlt hcard alt b)
      (P.slottedAlt_bound hcard alt hAlt b)).rawInterval
      ((P.slotted hcard b).family.mainCoefficient cutoff
        (fun z => v (sourceReferenceToPhysical T.slope z))
        (fun z => g (sourceReferenceToPhysical T.slope z))) 0 lower upper
  have hdiff (b : Fin B) : DifferentiableAt ℝ (fun x => F b x y) z.1 := by
    exact lattice_rawInterval_horizontal_differentiable
      ((P.slotted hcard b).withProfile (P.slottedAlt hcard alt b)
        (P.slottedAlt_bound hcard alt hAlt b))
      ((P.slotted hcard b).family.mainCoefficient cutoff
        (fun z => v (sourceReferenceToPhysical T.slope z))
        (fun z => g (sourceReferenceToPhysical T.slope z)))
      0 lower upper hlu z.1 y
  have hsum : (fun x => Q.rawInterval coeff 0 lower upper x y) =
      fun x => ∑ b : Fin B, F b x y := by
    funext x
    exact (P.sum_slotted_cross_rawInterval hcard alt hAlt T.slope cutoff v g
      0 lower upper x y).symm
  have hdiffsum : deriv (fun x => Q.rawInterval coeff 0 lower upper x y) z.1 =
      ∑ b : Fin B, deriv (fun x => F b x y) z.1 := by
    rw [hsum]
    exact deriv_fun_sum (fun b _ => hdiff b)
  have hb (b : Fin B) : ‖deriv (fun x => F b x y) z.1‖ ≤
      (L ^ (2 * p + 3) / r) * (T.weight K (D : ℝ) z) ^ 8 := by
    have hR : (P.slotted hcard b).constant ≤ L ^ p := by
      simpa only [P.slotted_constant hcard] using hP
    have hv' : Measurable (fun z => v (sourceReferenceToPhysical T.slope z)) :=
      hv.comp (sourceReferenceToPhysical T.slope).measurable
    have hg' : Measurable (fun z => g (sourceReferenceToPhysical T.slope z)) :=
      hg.comp (sourceReferenceToPhysical T.slope).measurable
    exact hderivative L ((le_max_left _ _).trans hLL) N κ (P.SlotItem hcard b)
      (P.slotted hcard b) hR
      (P.slottedAlt hcard alt b) (P.slottedAlt_bound hcard alt hAlt b) T K hK
      (P.slotted_topGeometry hcard G b) cutoff
      (fun z => v (sourceReferenceToPhysical T.slope z)) hv'
      (fun z => g (sourceReferenceToPhysical T.slope z)) hg' (fun z => hg1 _)
      lower upper hlu r hr (fun j hj hj' => hs j hj hj') z
  change ‖deriv (fun x => Q.rawInterval coeff 0 lower upper x y) z.1‖ ≤ _
  rw [hdiffsum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _b : Fin B, (L ^ (2 * p + 3) / r) * (T.weight K (D : ℝ) z) ^ 8 :=
      Finset.sum_le_sum (fun b _ => hb b)
    _ = ((B : ℝ) * L ^ (2 * p + 3) / r) * (T.weight K (D : ℝ) z) ^ 8 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    _ ≤ _ := by
      have hexp : (B : ℝ) * L ^ (2 * p + 3) ≤ L ^ (2 * p + 4) := by
        calc
          _ ≤ L * L ^ (2 * p + 3) :=
            mul_le_mul_of_nonneg_right hBL (Real.rpow_nonneg hLpos.le _)
          _ = L ^ (2 * p + 4) := by
            calc
              _ = L ^ (1 : ℝ) * L ^ (2 * p + 3) := by rw [Real.rpow_one]
              _ = L ^ (1 + (2 * p + 3)) := (Real.rpow_add hLpos _ _).symm
              _ = _ := by congr 1; ring
      exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hexp hr.le) (by positivity)

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
