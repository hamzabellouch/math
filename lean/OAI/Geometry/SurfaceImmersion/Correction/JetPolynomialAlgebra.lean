import OAI.Geometry.SurfaceImmersion.Geometry.LowJetChainRule
import OAI.Geometry.SurfaceImmersion.Primitive.LocalPeriodicCalculus

namespace OAI

/-! Finite polynomials in actual coordinate jets, with coefficients smooth in
position, the second jet, and the periodic variable. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial

/-- A sum of monomials. Jet factors are independent of the angular variable. -/
inductive Expression where
  | coeff (c : LowJet × ℝ → ℝ)
  | atom (word : List (Fin 2)) (component : Fin 4) (tail : Expression)
  | add (left right : Expression)

namespace Expression

def eval : Expression → (Base → Space) → Base × ℝ → ℝ
  | .coeff c, G, z => c (lowJet G z.1, z.2)
  | .atom w a e, G, z => jet G w a z.1 * eval e G z
  | .add e f, G, z => eval e G z + eval f G z

def mapCoeff (f : (LowJet × ℝ → ℝ) → (LowJet × ℝ → ℝ)) : Expression → Expression
  | .coeff c => .coeff (f c)
  | .atom w a e => .atom w a (mapCoeff f e)
  | .add e g => .add (mapCoeff f e) (mapCoeff f g)

def mul : Expression → Expression → Expression
  | .coeff c, f => mapCoeff (fun d z => c z * d z) f
  | .atom w a e, f => .atom w a (mul e f)
  | .add e g, f => .add (mul e f) (mul g f)

/-- Largest order of a jet factor. Coefficients themselves use jets through order two. -/
def order : Expression → ℕ
  | .coeff _ => 2
  | .atom w _ e => max w.length e.order
  | .add e f => max e.order f.order

/-- Scale loss when the second jet is controlled. -/
def loss : Expression → ℕ
  | .coeff _ => 0
  | .atom w _ e => (w.length - 2) + e.loss
  | .add e f => max e.loss f.loss

def SmoothCoeffs (O : Set LowJet) : Expression → Prop
  | .coeff c => ContDiffOn ℝ ∞ c (O ×ˢ Set.univ)
  | .atom _ _ e => e.SmoothCoeffs O
  | .add e f => e.SmoothCoeffs O ∧ f.SmoothCoeffs O

lemma eval_mapCoeff_mul (e : Expression) (G : Base → Space) (c : LowJet × ℝ → ℝ)
    (z : Base × ℝ) :
    (e.mapCoeff (fun d x => c x * d x)).eval G z = c (lowJet G z.1, z.2) * e.eval G z := by
  induction e with
  | coeff d => rfl
  | atom w a e ih => simp only [mapCoeff, eval, ih]; ring
  | add e f ihe ihf => simp only [mapCoeff, eval, ihe, ihf]; ring

lemma eval_mul (e f : Expression) (G : Base → Space) (z : Base × ℝ) :
    (e.mul f).eval G z = e.eval G z * f.eval G z := by
  induction e with
  | coeff c => exact eval_mapCoeff_mul f G c z
  | atom w a e ih => simp only [mul, eval, ih]; ring
  | add e g ihe ihg => simp only [mul, eval, ihe, ihg]; ring

@[simp] lemma order_mapCoeff (e : Expression) (f) : (e.mapCoeff f).order = e.order := by
  induction e with
  | coeff c => rfl
  | atom w a e ih => simp only [mapCoeff, order, ih]
  | add e g ihe ihg => simp only [mapCoeff, order, ihe, ihg]

@[simp] lemma loss_mapCoeff (e : Expression) (f) : (e.mapCoeff f).loss = e.loss := by
  induction e with
  | coeff c => rfl
  | atom w a e ih => simp only [mapCoeff, loss, ih]
  | add e g ihe ihg => simp only [mapCoeff, loss, ihe, ihg]

lemma order_mul_le (e f : Expression) : (e.mul f).order ≤ max e.order f.order := by
  induction e with
  | coeff c => simp only [mul, order_mapCoeff, order]; exact le_max_right _ _
  | atom w a e ih => simp only [mul, order] at *; omega
  | add e g ihe ihg => simp only [mul, order] at *; omega

lemma loss_mul_le (e f : Expression) : (e.mul f).loss ≤ e.loss + f.loss := by
  induction e with
  | coeff c => simp only [mul, loss_mapCoeff, loss, zero_add, le_refl]
  | atom w a e ih => simp only [mul, loss] at *; omega
  | add e g ihe ihg => simp only [mul, loss] at *; omega

lemma smoothCoeffs_map {O : Set LowJet} (e : Expression) (f)
    (hf : ∀ c, ContDiffOn ℝ ∞ c (O ×ˢ Set.univ) → ContDiffOn ℝ ∞ (f c) (O ×ˢ Set.univ))
    (he : e.SmoothCoeffs O) : (e.mapCoeff f).SmoothCoeffs O := by
  induction e with
  | coeff c => exact hf c he
  | atom w a e ih => exact ih he
  | add e g ihe ihg => exact ⟨ihe he.1, ihg he.2⟩

lemma smoothCoeffs_mul {O : Set LowJet} {e f : Expression}
    (he : e.SmoothCoeffs O) (hf : f.SmoothCoeffs O) : (e.mul f).SmoothCoeffs O := by
  induction e with
  | coeff c => exact smoothCoeffs_map f _ (fun d hd => he.mul hd) hf
  | atom w a e ih => exact ih he
  | add e g ihe ihg => exact ⟨ihe he.1, ihg he.2⟩

lemma eval_smooth {O : Set LowJet} {S : Set Base} {G : Base → Space}
    (hG : ContDiff ℝ ∞ G) (hQ : Set.MapsTo (lowJet G) S O)
    {e : Expression} (he : e.SmoothCoeffs O) :
    ContDiffOn ℝ ∞ (e.eval G) (S ×ˢ Set.univ) := by
  induction e with
  | coeff c =>
    exact he.comp (((lowJet_smooth hG).comp contDiff_fst).prodMk contDiff_snd).contDiffOn
      (fun z hz => ⟨hQ hz.1, Set.mem_univ _⟩)
  | atom w a e ih =>
    exact (((jet_smooth hG w a).comp contDiff_fst).contDiffOn).mul (ih he)
  | add e f ihe ihf => exact (ihe he.1).add (ihf he.2)

end Expression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
