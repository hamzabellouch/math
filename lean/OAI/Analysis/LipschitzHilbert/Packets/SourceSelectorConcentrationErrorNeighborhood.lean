import OAI.Analysis.LipschitzHilbert.Packets.SourceSelectorConcentrationErrorMoments
import OAI.Analysis.LipschitzHilbert.Estimates.GlobalNeighborhood

namespace OAI

/-! The positive angular-error moments control covariant vertical
neighborhoods of polynomially weighted packet sums. There is no Fourier
or martingale hypothesis in this step. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LipschitzHilbert.LabeledAngularErrorFamily
variable {N : ℕ} {Λ : Fin N → Type} {κ : Type} {ι : ∀ j, Λ j → Type}
  [∀ j, Fintype (Λ j)] [Fintype κ] [∀ j b, Fintype (ι j b)]

theorem error_global_neighborhood {α : Type*}
    (P : LabeledAngularErrorFamily N Λ κ ι)
    (B C a b r R : ℝ) (hB : 0 ≤ B) (hC : 0 < C) (hr : 0 < r) (hR : 0 < R)
    (hs : ∀ y, (P.sources y).sourceBound ≤ B)
    (ht : ∀ y, (P.sources y).sumBound ≤ B)
    (hshort : ∀ j l (_u : ι j l), P.length j ≤ r)
    (frequency : κ → ℝ) (f : α → κ → ℝ → ℝ → ℂ)
    (F : α → ℝ → ℝ → EuclideanSpace ℂ κ)
    (q n : ℕ) (hq : 1 ≤ q) (hn : 1 ≤ n)
    (hdiff : ∀ i k x y, DifferentiableAt ℝ (f i k x) y)
    (hmem : ∀ (p : ℤ×ℤ) i x, MemLp (covariantSignal frequency (fun k => f i k x)) 2
      (volume.restrict (Icc (b+R*p.2-2*R) (b+R*p.2+2*R))))
    (hbV : ∀ i x y, ‖(WithLp.toLp 2 (fun k => f i k x y) : EuclideanSpace ℂ κ)‖ ≤
      C*P.error y x)
    (hbD : ∀ i x y, 4*R*‖covariantSignal frequency (fun k => f i k x) y‖ ≤
      C*P.error y x)
    (hweighted : ∀ i x y,
      ‖(WithLp.toLp 2 (fun k => f i k x y) : EuclideanSpace ℂ κ)‖ =
        (polynomialWeight a r q x*polynomialWeight b R q y)*‖F i x y‖) :
    ∃ bad : Set (ℝ×ℝ), MeasurableSet bad ∧
      (volume.prod volume) bad ≤ (1/4:ℝ≥0∞)^n*
        (2*ENNReal.ofReal r*ENNReal.ofReal (2*R))*ENNReal.ofReal ((4*Real.pi)^2) ∧
      ∀ i x z v, |v| ≤ R → (x,z) ∉ bad →
        ‖F i x (z+v)‖ ≤
          256^q*(8*C*selectorErrorMomentBase B*(n:ℝ))*
            boxVariationWeight (packetBoxIndex a b r R x z)^(q-1) := by
  let V : ℝ×ℝ → ℝ := fun z => C*P.error z.1 z.2
  let D : ℝ×ℝ → ℝ := fun z => V z/(4*R)
  let A := C*selectorErrorMomentBase B*(2*n:ℕ)
  have hV : Continuous V := continuous_const.mul P.error_joint_continuous
  have hD : Continuous D := hV.div_const _
  have hn0 : (0:ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hA : 0 < A := by
    have := selectorErrorMomentBase_pos hB
    dsimp [A]
    positivity
  have hscale (y x : ℝ) : 4*R*D (y,x) = V (y,x) := by
    dsimp [D]
    field_simp
  have hVnonneg (z : ℝ×ℝ) : 0 ≤ V z := mul_nonneg hC.le (P.error_nonneg z.1 z.2)
  have hline (p : ℤ×ℤ) (y : ℝ) :
      (∫⁻ x in Ico (a+r*p.1) (a+r*((p.1:ℝ)+1)),
        ENNReal.ofReal (V (y,x)^(2*n)+(4*R*D (y,x))^(2*n))) ≤
          2*(ENNReal.ofReal A)^(2*n)*ENNReal.ofReal r := by
    let grid : FiniteLineGrid := {
      branching := 2, branching_pos := by decide, origin := a+r*p.1,
      width := r, width_pos := hr, depth := 0 }
    have hroot : grid.root = Ico (a+r*p.1) (a+r*((p.1:ℝ)+1)) := by
      unfold FiniteLineGrid.root
      dsimp [grid]
      congr 1
      ring
    have hmass : grid.lineMeasure univ = ENNReal.ofReal r := by
      rw [FiniteLineGrid.lineMeasure,Measure.restrict_apply_univ,hroot,Real.volume_Ico]
      congr 1
      ring
    have hm := P.error_moment_uniform B hB hs ht grid rfl hshort y (2*n) (by omega)
    have hpow (x : ℝ) : ENNReal.ofReal (V (y,x)^(2*n)) =
        (ENNReal.ofReal C)^(2*n)*(ENNReal.ofReal (P.error y x))^(2*n) := by
      rw [ENNReal.ofReal_pow (hVnonneg (y,x))]
      change (ENNReal.ofReal (C*P.error y x))^(2*n) = _
      rw [ENNReal.ofReal_mul hC.le,mul_pow]
    have hsum (x : ℝ) : ENNReal.ofReal (V (y,x)^(2*n)+V (y,x)^(2*n)) =
        ENNReal.ofReal (V (y,x)^(2*n))+ENNReal.ofReal (V (y,x)^(2*n)) :=
      ENNReal.ofReal_add (pow_nonneg (hVnonneg (y,x)) _) (pow_nonneg (hVnonneg (y,x)) _)
    simp_rw [hscale,hsum,hpow]
    have he : Measurable (fun x : ℝ => P.error y x) :=
      (P.error_joint_continuous.comp
        ((continuous_const : Continuous (fun _ : ℝ => y)).prodMk continuous_id)).measurable
    rw [lintegral_add_left ((he.ennreal_ofReal.pow_const (2*n)).const_mul
      ((ENNReal.ofReal C)^(2*n)))]
    have hsingle : (∫⁻ x in Ico (a+r*p.1) (a+r*((p.1:ℝ)+1)),
        (ENNReal.ofReal C)^(2*n)*(ENNReal.ofReal (P.error y x))^(2*n)) ≤
          (ENNReal.ofReal A)^(2*n)*ENNReal.ofReal r := by
      rw [lintegral_const_mul' _ _ (by finiteness)]
      have h := mul_le_mul_right hm ((ENNReal.ofReal C)^(2*n))
      rw [hmass] at h
      rw [FiniteLineGrid.lineMeasure,hroot] at h
      apply h.trans_eq
      have hfactor : ENNReal.ofReal A = ENNReal.ofReal C*
          ENNReal.ofReal (selectorErrorMomentBase B*(2*n:ℕ)) := by
        dsimp [A]
        rw [show C*selectorErrorMomentBase B*(2*n:ℕ) =
          C*(selectorErrorMomentBase B*(2*n:ℕ)) by ring,ENNReal.ofReal_mul hC.le]
      rw [hfactor,mul_pow]
      ring
    calc
      _ ≤ ((ENNReal.ofReal A)^(2*n)*ENNReal.ofReal r)+
          ((ENNReal.ofReal A)^(2*n)*ENNReal.ofReal r) := add_le_add hsingle hsingle
      _ = _ := by ring
  obtain ⟨bad,hbad,harea,hpoint⟩ := global_top_neighborhood frequency f F V D hV hD
    a b r R A hr hR hA n q hn hq hline hdiff hmem hbV (by
      intro i x y
      apply (le_div_iff₀ (show 0 < 4*R by positivity)).mpr
      simpa only [mul_comm] using hbD i x y) hweighted
  refine ⟨bad,hbad,harea,?_⟩
  intro i x z v hv hout
  have h := hpoint i x z v hv hout
  convert h using 1
  dsimp [A]
  push_cast
  ring

end LipschitzHilbert.LabeledAngularErrorFamily

end

end OAI
