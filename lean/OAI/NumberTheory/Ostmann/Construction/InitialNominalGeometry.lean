import OAI.NumberTheory.Ostmann.Construction.InitialLogGeometry

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction

theorem initial_nominal_log_product_support {b s k : ℕ} (x : InitialCoordinates b s k)
    (hx : x.Positive) (G tb td J : ℝ) (w : Fin k → ℝ)
    (topCenter : Bool → Fin 3 → ℝ) (compCenter : Bool → Fin k → Fin 2 → ℝ)
    (hg : ∀h,|Real.log (x.giant h)-G|≤1)
    (hb : ∀h,|(∑i,Real.log (x.bulk h i))-tb|≤1)
    (hs : ∀h,|(∑i,Real.log (x.spectator h i))-td|≤1)
    (ht : ∀h i,|Real.log (x.top h i)-topCenter h i|≤1)
    (hc : ∀h j i,|Real.log (x.compensation h j i)-compCenter h j i|≤1)
    (et ec : ℝ) (htop : |(∑h,∑i,topCenter h i)-(J-2*tb)|≤et)
    (hcomp : |(∑h,∑j,∑i,compCenter h j i)-(∑j,w j)|≤ec) :
    |Real.log x.product-(2*G+2*td+J+∑j,w j)|≤12+4*(k:ℝ)+et+ec := by
  have h₀ := initial_log_product_support x hx G tb td topCenter compCenter hg hb hs ht hc
  let c := 2*G+2*tb+2*td+(∑h,∑i,topCenter h i)+(∑h,∑j,∑i,compCenter h j i)
  have he : Real.log x.product-(2*G+2*td+J+∑j,w j) =
      (Real.log x.product-c)+((∑h,∑i,topCenter h i)-(J-2*tb))+
      ((∑h,∑j,∑i,compCenter h j i)-(∑j,w j)) := by dsimp [c]; ring
  rw [he]
  have h₁ := abs_add_le (Real.log x.product-c)
    ((∑h,∑i,topCenter h i)-(J-2*tb))
  have h₂ := abs_add_le ((Real.log x.product-c)+((∑h,∑i,topCenter h i)-(J-2*tb)))
    ((∑h,∑j,∑i,compCenter h j i)-(∑j,w j))
  change |Real.log x.product-c|≤12+4*(k:ℝ) at h₀
  linarith

end Ostmann.Construction

end

end OAI
