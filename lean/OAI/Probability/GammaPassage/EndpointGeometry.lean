import OAI.Probability.GammaPassage.EndpointMesh
import OAI.Probability.GammaPassage.GridVerticalPaths

namespace OAI

/-! Fixed transverse targets and whole-extension support errors for
 gr:variable-endpoints. Rounding is charged once, independently of levels. -/
namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge GammaFPP.IntervalTravelBridge

open Set Finset

/-- Concatenate a finite deterministic list of connections, retaining every
vertex-localization condition and adding their actual traversal costs. -/
theorem exists_path_chain (w : Edge → ℝ) (p : ℕ → Vertex) (S : Set Vertex)
    (a : ℕ → ℝ) (n : ℕ) (hp : p 0 ∈ S)
    (h : ∀ i < n, ∃ ds, p i+displacement ds=p (i+1) ∧
      pathCost w (p i) ds ≤ a i ∧ PathIn (p i) ds S) :
    ∃ ds, p 0+displacement ds=p n ∧
      pathCost w (p 0) ds ≤ ∑ i ∈ range n, a i ∧ PathIn (p 0) ds S := by
  induction n with
  | zero =>
    refine ⟨[],by simp,by simp [pathCost],?_⟩
    intro i hi
    simpa using hp
  | succ n ih =>
    obtain ⟨ds,hd,hcostd,hind⟩ := ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    obtain ⟨es,he,hcoste,hine⟩ := h n (Nat.lt_succ_self n)
    refine ⟨ds++es,?_,?_,?_⟩
    · rw [displacement_append, ← add_assoc, hd]
      exact he
    · rw [pathCost_append, hd, sum_range_succ]
      exact add_le_add hcostd hcoste
    · apply pathIn_append _ _ _ _ hind
      simpa only [hd] using hine

noncomputable def endpointVertex (b r : ℝ) (X : ℤ) : Vertex := (X,⌊b*X+r⌋)

lemma endpointVertex_error (b r : ℝ) (X : ℤ) :
    -1 < transverse b (endpointVertex b r X)-r ∧
      transverse b (endpointVertex b r X)-r ≤ 0 := by
  have hl := Int.floor_le (b*X+r)
  have hu := Int.lt_floor_add_one (b*X+r)
  dsimp [transverse,endpointVertex]
  constructor <;> linarith

lemma endpointVertex_close (b r : ℝ) (X : ℤ) :
    |transverse b (endpointVertex b r X)-r| < 1 := by
  have h := endpointVertex_error b r X
  exact abs_lt.mpr ⟨h.1,by linarith [h.2]⟩

lemma endpointVertex_self (b : ℝ) (p : Vertex) :
    endpointVertex b (transverse b p) p.1=p := by
  apply Prod.ext
  · rfl
  · simp [endpointVertex,transverse]

lemma endpointVertex_displacement (b r : ℝ) (X Y : ℤ) :
    |transverse b (endpointVertex b r Y-endpointVertex b r X)| < 1 := by
  have hx := endpointVertex_error b r X
  have hy := endpointVertex_error b r Y
  have he : transverse b (endpointVertex b r Y-endpointVertex b r X) =
      transverse b (endpointVertex b r Y)-transverse b (endpointVertex b r X) := by
    simp [transverse]; ring
  rw [he,abs_lt]
  constructor <;> linarith [hx.1,hx.2,hy.1,hy.2]

lemma endpoint_path_defect (w : Edge → ℝ) (b r m₀ a E : ℝ) (X Y : ℤ)
    (ds : List Step)
    (hd : endpointVertex b r X+displacement ds=endpointVertex b r Y)
    (hc : pathCost w (endpointVertex b r X) ds ≤ m₀*((Y-X : ℤ) : ℝ)+E) :
    defect w b m₀ a (endpointVertex b r X) ds ≤ E+|a| := by
  have hd' : displacement ds=endpointVertex b r Y-endpointVertex b r X := by
    rw [← hd]; abel
  have hr := (endpointVertex_displacement b r X Y).le
  have hm : |a*transverse b (endpointVertex b r Y-endpointVertex b r X)| ≤ |a| := by
    rw [abs_mul]
    nlinarith [abs_nonneg a]
  have hlo := (abs_le.mp hm).1
  unfold defect support
  rw [hd']
  have hx : (endpointVertex b r Y-endpointVertex b r X).1=Y-X := rfl
  rw [hx]
  linarith

/-- Reverse-displacement estimate for a negative-defect path, allowing
unordered endpoints. -/
lemma negative_defect_reverse_span (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (b m₀ a R s ε : ℝ) (hm : 0 < m₀) (_hR : 0 ≤ R) (hs : 0 ≤ s) (hε : 0 ≤ ε)
    (p z : Vertex) (ds : List Step) (hd : p+displacement ds=z)
    (hp : |transverse b p| ≤ R*s) (hz : |transverse b z| ≤ R*s)
    (hc : defect w b m₀ a p ds < -ε*s) :
    -2*R*|a| *s/m₀ ≤ ((z.1-p.1 : ℤ) : ℝ) := by
  have hd' : displacement ds=z-p := by rw [← hd]; abel
  have hr : |transverse b (z-p)| ≤ 2*R*s := by
    have he : transverse b (z-p)=transverse b z-transverse b p := by simp [transverse]; ring
    rw [he]
    exact (abs_sub _ _).trans (by linarith)
  have ha : a*transverse b (z-p) ≤ 2*R*|a| *s := by
    have hh := mul_le_mul_of_nonneg_left hr (abs_nonneg a)
    have hb := le_abs_self (a*transverse b (z-p))
    rw [abs_mul] at hb
    nlinarith
  have hcost := pathCost_nonneg hw p ds
  have heps := mul_nonneg hε hs
  unfold defect support at hc
  rw [hd'] at hc
  change pathCost w p ds-(m₀*((z.1-p.1 : ℤ) : ℝ)+a*transverse b (z-p)) < -ε*s at hc
  apply (div_le_iff₀ hm).mpr
  nlinarith

lemma extended_columns_span (p z : ℤ) (m J : ℕ) (C s : ℝ)
    (hrev : -C*s ≤ ((z-p : ℤ) : ℝ))
    (hscale : C*s ≤ (gridMesh m J : ℝ)) :
    (gridMesh m J : ℝ) ≤ ((exitColumn z m J-entranceColumn p m J : ℤ) : ℝ) := by
  have hp := entranceColumn_span p m J
  have hz := exitColumn_span z m J
  have hp' : (gridMesh m J : ℝ) ≤ ((p-entranceColumn p m J : ℤ) : ℝ) := by exact_mod_cast hp.1
  have hz' : (gridMesh m J : ℝ) ≤ ((exitColumn z m J-z : ℤ) : ℝ) := by exact_mod_cast hz.1
  push_cast at hp' hz' hrev ⊢
  linarith

end GammaFPP.CrossingBridge

end OAI
