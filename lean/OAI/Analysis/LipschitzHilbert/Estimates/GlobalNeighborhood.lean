import OAI.Analysis.LipschitzHilbert.Estimates.GlobalTopBoxes
import OAI.Analysis.LipschitzHilbert.Estimates.TopNeighborhood

namespace OAI

/-! Global top concentration from uniform local line moments. Box
exceptions are constructed by the proved vertical Sobolev estimate,
and their areas are summed over the whole plane. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace LipschitzHilbert

theorem global_top_neighborhood {α κ E : Type*} [Fintype κ] [NormedAddCommGroup E]
    (frequency : κ → ℝ) (f : α → κ → ℝ → ℝ → ℂ) (F : α → ℝ → ℝ → E)
    (V D : ℝ × ℝ → ℝ) (hV : Continuous V) (hD : Continuous D)
    (a b r R A : ℝ) (hr : 0 < r) (hR : 0 < R) (hA : 0 < A)
    (n q : ℕ) (hn : 1 ≤ n) (hq : 1 ≤ q)
    (hline : ∀ (p : ℤ × ℤ) y, (∫⁻ x in Ico (a+r*p.1) (a+r*((p.1:ℝ)+1)),
      ENNReal.ofReal (V (y,x)^(2*n)+(4*R*D (y,x))^(2*n))) ≤
        2*(ENNReal.ofReal A)^(2*n)*ENNReal.ofReal r)
    (hdiff : ∀ i k x y, DifferentiableAt ℝ (f i k x) y)
    (hmem : ∀ (p : ℤ × ℤ) i x, MemLp (covariantSignal frequency (fun k => f i k x)) 2
      (volume.restrict (Icc (b+R*p.2-2*R) (b+R*p.2+2*R))))
    (hbV : ∀ i x y, ‖(WithLp.toLp 2 (fun k => f i k x y) : EuclideanSpace ℂ κ)‖ ≤ V (y,x))
    (hbD : ∀ i x y, ‖covariantSignal frequency (fun k => f i k x) y‖ ≤ D (y,x))
    (hweighted : ∀ i x y, ‖(WithLp.toLp 2 (fun k => f i k x y) : EuclideanSpace ℂ κ)‖ =
      (polynomialWeight a r q x * polynomialWeight b R q y)*‖F i x y‖) :
    ∃ exceptional : Set (ℝ × ℝ), MeasurableSet exceptional ∧
      (volume.prod volume) exceptional ≤ (1/4:ℝ≥0∞)^n*
        (2*ENNReal.ofReal r*ENNReal.ofReal (2*R))*ENNReal.ofReal ((4*Real.pi)^2) ∧
      ∀ i x z v, |v| ≤ R → (x,z) ∉ exceptional →
        ‖F i x (z+v)‖ ≤ 256^q*(4*A)*
          boxVariationWeight (packetBoxIndex a b r R x z)^(q-1) := by
  have hlocal (p : ℤ × ℤ) := top_neighborhood_exceptional frequency f V D hV hD
    (Ico (a+r*p.1) (a+r*((p.1:ℝ)+1))) measurableSet_Ico (b+R*p.2) R
    (4*A/boxVariationWeight p) hR
    (div_nonneg (by positivity) (boxVariationWeight_pos p).le) n
    (2*(ENNReal.ofReal A)^(2*n)*ENNReal.ofReal r) (hline p)
    (fun i x y _ k => hdiff i k x y) (hmem p)
    (fun i x y _ => hbV i x y) (fun i x y _ => hbD i x y)
  choose bad hbad using hlocal
  apply global_top_box_gluing F bad (fun p => (hbad p).1) a b r R A hr hR hA
    (2*ENNReal.ofReal r*ENNReal.ofReal (2*R)) n q hn hq
  · intro p
    have h := (hbad p).2.2.1
    convert h using 1
    rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
    simp only [ENNReal.ofReal_ofNat, pow_mul]
    norm_num
    ring
  · intro p i x z v hx hz hv hout
    have h := (hbad p).2.2.2 i x z v hx hz hv hout
    rwa [hweighted] at h

end LipschitzHilbert

end

end OAI
