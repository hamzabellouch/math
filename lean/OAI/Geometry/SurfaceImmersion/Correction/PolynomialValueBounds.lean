import OAI.Geometry.SurfaceImmersion.Atlas.CoordinateTaylorIdentity
import OAI.Geometry.SurfaceImmersion.Atlas.WeightedPhaseExpressions
import OAI.Geometry.SurfaceImmersion.Geometry.LocalIsometryBounds
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialPerturbationCalculus

namespace OAI

/-! Uniform evaluation bounds for the polynomial part of the actual mean
metric. The loss is fixed by P, before any accuracy order is chosen. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates

lemma coordinatePolynomialValue_smooth {n : ℕ} {P : Fin 3 → Fin n → Expression}
    (hP : ∀ k l, (P k l).SmoothCoeffs Set.univ) {G : Base → Space}
    (hG : ContDiff ℝ ∞ G) (ε : ℝ) :
    ContDiff ℝ ∞ (coordinatePolynomialValue P ε G 0) := by
  apply contDiff_pi.mpr
  intro k
  have hs : ContDiff ℝ ∞ (fun p : Base => eval (P k) ε G (p,0)) := by
    have he : ContDiff ℝ ∞ (eval (P k) ε G) := contDiffOn_univ.mp (by
      simpa only [Set.univ_prod_univ] using
        (eval_smooth (U := Set.univ) (hP k) ε hG (fun _ _ => Set.mem_univ _)))
    exact he.comp (contDiff_id.prodMk contDiff_const)
  change ContDiff ℝ ∞ ((fun p : Base => eval (P k) ε G (p,0)) ∘ planeCoordinateIsometry.symm)
  exact hs.comp planeCoordinateIsometry.symm.contDiff

theorem coordinatePolynomialValue_bound {n : ℕ} {Q : Set LowJet}
    (hQ : IsCompact Q) (P : Fin 3 → Fin n → Expression)
    (hP : ∀ k l, (P k l).SmoothCoeffs Set.univ) (m : ℕ) (B : ℝ) (hB : 1 ≤ B) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (U : Set Base), IsOpen U →
      ∀ {G : Base → Space}, ContDiff ℝ ∞ G → Set.MapsTo (lowJet G) U Q →
      ∀ (s ε : ℝ), 0 < s → s ≤ 1 → 0 ≤ ε → ε ≤ 1 →
      WeightedBound U s (m + tensorOrder P) B (lowJet G) →
      WeightedBound (planeCoordinateIsometry.symm ⁻¹' U) s m
        (D * ε / s ^ tensorLoss P) (coordinatePolynomialValue P ε G 0) := by
  classical
  choose D hD hd using fun k l => Expression.compact_phase_bound isOpen_univ hQ
    (Set.subset_univ _) (P k l) (hP k l) m B 1 hB le_rfl
  let E : ℝ := ∑ k, ∑ l, D k l
  have hE : 0 ≤ E := Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ => hD k l
  refine ⟨E,hE,?_⟩
  intro U hU G hG hGQ s ε hs hs1 hε hε1 hGb
  have ho (k : Fin 3) (l : Fin n) : (P k l).order ≤ tensorOrder P :=
    (Finset.le_sup (f := fun l => (P k l).order) (Finset.mem_univ l)).trans
      (Finset.le_sup (f := fun k => order (P k)) (Finset.mem_univ k))
  have hl (k : Fin 3) (l : Fin n) : (P k l).loss ≤ tensorLoss P := by
    have h₁ := Finset.le_sup (f := fun l => (P k l).loss + 6) (Finset.mem_univ l)
    change (P k l).loss + 6 ≤ loss (P k) at h₁
    have h₂ := Finset.le_sup (f := fun k => loss (P k)) (Finset.mem_univ k)
    change _ ≤ tensorLoss P at h₂
    exact (by omega : (P k l).loss ≤ loss (P k)).trans h₂
  have hsmooth (k : Fin 3) (l : Fin n) :
      ContDiff ℝ ∞ (fun p : Base => (P k l).eval G (p,0)) := by
    have hh := (P k l).eval_smooth (S := Set.univ) hG
      (fun _ _ => Set.mem_univ _) (hP k l)
    have hh' : ContDiff ℝ ∞ ((P k l).eval G) :=
      contDiffOn_univ.mp (by simpa only [Set.univ_prod_univ] using hh)
    exact hh'.comp (contDiff_id.prodMk contDiff_const)
  have hb (k : Fin 3) (l : Fin n) : WeightedBound U s m
      (D k l * ε / s ^ tensorLoss P) (fun x => ε^(l.val+1) * (P k l).eval G (x,0)) := by
    have he := hd k l U hU G (fun _ => 0) s s hs le_rfl hs1 hG contDiffOn_const hGQ
      (fun _ _ => by constructor <;> norm_num)
      (hGb.mono_order (Nat.add_le_add_left (ho k l) m))
      ((weightedBound_zero U s m (F := ℝ)).mono_const zero_le_one)
    have he' := he.const_smul hU.uniqueDiffOn (hsmooth k l).contDiffOn (ε^(l.val+1))
    apply (he'.congr (fun _ _ => by simp only [smul_eq_mul])).mono_const
    rw [abs_of_nonneg (pow_nonneg hε _)]
    have hp : ε^(l.val+1) ≤ ε := by
      simpa only [pow_one] using
        pow_le_pow_of_le_one hε hε1 (by omega : 1 ≤ l.val+1)
    calc
      _ ≤ ε * (D k l / s^(P k l).loss) := mul_le_mul_of_nonneg_right hp
        (div_nonneg (hD k l) (pow_nonneg hs.le _))
      _ ≤ ε * (D k l / s^tensorLoss P) := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_left (hD k l) (pow_pos hs _)
          (pow_le_pow_of_le_one hs.le hs1 (hl k l))) hε
      _ = _ := by ring
  have hsum (k : Fin 3) : WeightedBound U s m
      ((∑ l, D k l) * ε / s^tensorLoss P) (fun x => eval (P k) ε G (x,0)) := by
    have hh := WeightedBound.finset_sum hU.uniqueDiffOn hs.le Finset.univ
      (fun l => D k l * ε / s^tensorLoss P)
      (fun l x => ε^(l.val+1) * (P k l).eval G (x,0))
      (fun l _ => ((hsmooth k l).const_smul (ε^(l.val+1))).contDiffOn)
      (fun l _ => hb k l)
    simpa only [eval,← Finset.sum_mul,← Finset.sum_div] using hh
  have hsource : WeightedBound U s m (E*ε/s^tensorLoss P)
      (fun x k => eval (P k) ε G (x,0)) := by
    apply WeightedBound.pi hU.uniqueDiffOn hs (by positivity)
    · intro k
      exact (ContDiff.sum (fun l _ => (hsmooth k l).const_smul (ε^(l.val+1)))).contDiffOn
    · intro k
      apply (hsum k).mono_const
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (Finset.single_le_sum (fun k _ => Finset.sum_nonneg fun l _ => hD k l)
            (Finset.mem_univ k)) hε) (pow_nonneg hs.le _)
  have hsourceSmooth : ContDiff ℝ ∞ (fun x k => eval (P k) ε G (x,0)) := by
    apply contDiff_pi.mpr
    intro k
    exact ContDiff.sum (fun l _ => (hsmooth k l).const_smul (ε^(l.val+1)))
  exact weightedBound_comp_isometry_on planeCoordinateIsometry.symm hU hsourceSmooth hsource

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
