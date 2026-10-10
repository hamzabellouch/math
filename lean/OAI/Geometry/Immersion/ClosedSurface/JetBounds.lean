import OAI.Geometry.Immersion.ClosedSurface.ModeBounds

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.SmallModes
open ClosedSurfaceR4.WeightedEstimates




abbrev TwoJet (n : ℕ) := Fin 5 → Ambient n

def twoJet {n : ℕ} (G : Field n) (p : Base) : TwoJet n :=
  ![coordDeriv dx G p, coordDeriv dy G p, coordDeriv dx (coordDeriv dx G) p,
    coordDeriv dx (coordDeriv dy G) p, coordDeriv dy (coordDeriv dy G) p]

namespace LowJet
variable {n : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma contDiffAt_dot {F G : E → Ambient n} {p : E}
    (hF : ContDiffAt ℝ ∞ F p) (hG : ContDiffAt ℝ ∞ G p) :
    ContDiffAt ℝ ∞ (fun q => F q ⬝ᵥ G q) p := by
  unfold dotProduct
  exact ContDiffAt.sum fun i _ => (contDiffAt_pi.mp hF i).mul (contDiffAt_pi.mp hG i)

lemma contDiffAt_cdiv {a b : E → ℂ} {p : E}
    (ha : ContDiffAt ℝ ∞ a p) (hb : ContDiffAt ℝ ∞ b p) (hne : b p ≠ 0) :
    ContDiffAt ℝ ∞ (fun q => a q / b q) p := by
  simp only [div_eq_mul_inv]
  exact ha.mul (hb.fun_inv hne)

lemma contDiffAt_gramDet {X Y : E → Ambient n} {p : E}
    (hX : ContDiffAt ℝ ∞ X p) (hY : ContDiffAt ℝ ∞ Y p) :
    ContDiffAt ℝ ∞ (fun q => gramDet (X q) (Y q)) p :=
  ((contDiffAt_dot hX hX).mul (contDiffAt_dot hY hY)).sub ((contDiffAt_dot hX hY).pow 2)

lemma contDiffAt_liftX {X Y : E → Ambient n} {ux uy : E → ℂ} {p : E}
    (hX : ContDiffAt ℝ ∞ X p) (hY : ContDiffAt ℝ ∞ Y p)
    (hx : ContDiffAt ℝ ∞ ux p) (hy : ContDiffAt ℝ ∞ uy p)
    (hD : gramDet (X p) (Y p) ≠ 0) :
    ContDiffAt ℝ ∞ (fun q => liftX (X q) (Y q) (ux q) (uy q)) p :=
  contDiffAt_cdiv (((contDiffAt_dot hY hY).mul hx).sub ((contDiffAt_dot hX hY).mul hy))
    (contDiffAt_gramDet hX hY) hD

lemma contDiffAt_liftY {X Y : E → Ambient n} {ux uy : E → ℂ} {p : E}
    (hX : ContDiffAt ℝ ∞ X p) (hY : ContDiffAt ℝ ∞ Y p)
    (hx : ContDiffAt ℝ ∞ ux p) (hy : ContDiffAt ℝ ∞ uy p)
    (hD : gramDet (X p) (Y p) ≠ 0) :
    ContDiffAt ℝ ∞ (fun q => liftY (X q) (Y q) (ux q) (uy q)) p :=
  contDiffAt_cdiv (((contDiffAt_dot hX hX).mul hy).sub ((contDiffAt_dot hX hY).mul hx))
    (contDiffAt_gramDet hX hY) hD

lemma contDiffAt_tangentLift {X Y : E → Ambient n} {ux uy : E → ℂ} {p : E}
    (hX : ContDiffAt ℝ ∞ X p) (hY : ContDiffAt ℝ ∞ Y p)
    (hx : ContDiffAt ℝ ∞ ux p) (hy : ContDiffAt ℝ ∞ uy p)
    (hD : gramDet (X p) (Y p) ≠ 0) :
    ContDiffAt ℝ ∞ (fun q => tangentLift (X q) (Y q) (ux q) (uy q)) p :=
  ((contDiffAt_liftX hX hY hx hy hD).smul hX).add ((contDiffAt_liftY hX hY hx hy hD).smul hY)

lemma contDiffAt_normalPart {X Y W : E → Ambient n} {p : E}
    (hX : ContDiffAt ℝ ∞ X p) (hY : ContDiffAt ℝ ∞ Y p) (hW : ContDiffAt ℝ ∞ W p)
    (hD : gramDet (X p) (Y p) ≠ 0) :
    ContDiffAt ℝ ∞ (fun q => normalPart (X q) (Y q) (W q)) p :=
  hW.sub (contDiffAt_tangentLift hX hY (contDiffAt_dot hX hW) (contDiffAt_dot hY hW) hD)



structure Domain (V : Set (TwoJet n)) : Prop where
  isOpen : IsOpen V
  determinant : ∀ J ∈ V, gramDet (J 0) (J 1) ≠ 0
  good : ∀ J ∈ V,
    normalPart (J 0) (J 1) (J 4) ⬝ᵥ normalPart (J 0) (J 1) (J 4) ≠ 0

def scalarCoefficients (J : TwoJet n) : Fin 8 → ℂ :=
  let X := J 0
  let Y := J 1
  let b := normalPart X Y (J 4)
  ![liftX X Y (X ⬝ᵥ J 2) (Y ⬝ᵥ J 2), liftY X Y (X ⬝ᵥ J 2) (Y ⬝ᵥ J 2),
    liftX X Y (X ⬝ᵥ J 3) (Y ⬝ᵥ J 3), liftY X Y (X ⬝ᵥ J 3) (Y ⬝ᵥ J 3),
    liftX X Y (X ⬝ᵥ J 4) (Y ⬝ᵥ J 4), liftY X Y (X ⬝ᵥ J 4) (Y ⬝ᵥ J 4),
    (normalPart X Y (J 2) ⬝ᵥ b) / (b ⬝ᵥ b),
    (normalPart X Y (J 3) ⬝ᵥ b) / (b ⬝ᵥ b)]

def vectorCoefficients (J : TwoJet n) : Fin 5 → Ambient n :=
  let X := J 0
  let Y := J 1
  let b := normalPart X Y (J 4)
  ![normalPart X Y (J 2), normalPart X Y (J 3), tangentLift X Y 1 0,
    tangentLift X Y 0 1, (b ⬝ᵥ b)⁻¹ • b]

abbrev CoeffIndex (n : ℕ) := Fin 8 ⊕ (Fin 5 × Fin n)

def coefficients (J : TwoJet n) : CoeffIndex n → ℂ
  | Sum.inl i => scalarCoefficients J i
  | Sum.inr (i, a) => vectorCoefficients J i a

lemma contDiffAt_scalarCoefficients {J : TwoJet n}
    (hD : gramDet (J 0) (J 1) ≠ 0)
    (hb : normalPart (J 0) (J 1) (J 4) ⬝ᵥ normalPart (J 0) (J 1) (J 4) ≠ 0) :
    ContDiffAt ℝ ∞ scalarCoefficients J := by
  have h (i : Fin 5) : ContDiffAt ℝ ∞ (fun A : TwoJet n => A i) J := contDiffAt_apply ℝ (Ambient n) i J
  have hX (i : Fin 5) := contDiffAt_liftX (h 0) (h 1)
    (contDiffAt_dot (h 0) (h i)) (contDiffAt_dot (h 1) (h i)) hD
  have hY (i : Fin 5) := contDiffAt_liftY (h 0) (h 1)
    (contDiffAt_dot (h 0) (h i)) (contDiffAt_dot (h 1) (h i)) hD
  have hn (i : Fin 5) := contDiffAt_normalPart (h 0) (h 1) (h i) hD
  have hr (i : Fin 5) := contDiffAt_cdiv (contDiffAt_dot (hn i) (hn 4))
    (contDiffAt_dot (hn 4) (hn 4)) hb
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · exact hX 2
  · exact hY 2
  · exact hX 3
  · exact hY 3
  · exact hX 4
  · exact hY 4
  · exact hr 2
  · exact hr 3

lemma contDiffAt_vectorCoefficients {J : TwoJet n}
    (hD : gramDet (J 0) (J 1) ≠ 0)
    (hb : normalPart (J 0) (J 1) (J 4) ⬝ᵥ normalPart (J 0) (J 1) (J 4) ≠ 0) :
    ContDiffAt ℝ ∞ vectorCoefficients J := by
  have h (i : Fin 5) : ContDiffAt ℝ ∞ (fun A : TwoJet n => A i) J := contDiffAt_apply ℝ (Ambient n) i J
  have hn (i : Fin 5) := contDiffAt_normalPart (h 0) (h 1) (h i) hD
  have ht (a b : ℂ) := contDiffAt_tangentLift (h 0) (h 1)
    (ux := fun _ => a) (uy := fun _ => b) contDiffAt_const contDiffAt_const hD
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · exact hn 2
  · exact hn 3
  · exact ht 1 0
  · exact ht 0 1
  · exact ((contDiffAt_dot (hn 4) (hn 4)).fun_inv hb).smul (hn 4)

lemma Domain.smoothCoefficients {V : Set (TwoJet n)} (h : Domain V) :
    ContDiffOn ℝ ∞ coefficients V := by
  intro J hJ
  apply ContDiffAt.contDiffWithinAt
  apply contDiffAt_pi.mpr
  intro i
  cases i with
  | inl i => exact contDiffAt_pi.mp (contDiffAt_scalarCoefficients (h.determinant J hJ) (h.good J hJ)) i
  | inr i =>
    exact contDiffAt_pi.mp
      (contDiffAt_pi.mp (contDiffAt_vectorCoefficients (h.determinant J hJ) (h.good J hJ)) i.1) i.2

end LowJet

lemma contDiffOn_twoJet {n : ℕ} {G : Field n} {U : Set Base} (hU : IsOpen U)
    (hG : ContDiffOn ℝ ∞ G U) : ContDiffOn ℝ ∞ (twoJet G) U := by
  intro p hp
  have h := (hG p hp).contDiffAt (hU.mem_nhds hp)
  apply ContDiffAt.contDiffWithinAt
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · exact contDiffAt_coordDeriv h dx
  · exact contDiffAt_coordDeriv h dy
  · exact contDiffAt_coordDeriv (contDiffAt_coordDeriv h dx) dx
  · exact contDiffAt_coordDeriv (contDiffAt_coordDeriv h dy) dx
  · exact contDiffAt_coordDeriv (contDiffAt_coordDeriv h dy) dy

lemma modeDomain_of_twoJet {n : ℕ} {G : Field n} {U : Set Base} {V : Set (TwoJet n)}
    (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G U) (hV : LowJet.Domain V)
    (hGV : MapsTo (twoJet G) U V) : ModeDomain G U :=
  by
  refine ⟨hU, hG, ?_, ?_⟩
  · intro p hp
    exact hV.determinant (twoJet G p) (hGV hp)
  · intro p hp
    exact hV.good (twoJet G p) (hGV hp)




theorem compact_reconstructionCoefficientBound {n : ℕ} {U : Set Base}
    (hU : IsOpen U) {Ω K : Set (TwoJet n)} (hΩ : LowJet.Domain Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) (m : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (G : Field n) (s C : ℝ), 0 < s → 1 ≤ C →
      ContDiffOn ℝ ∞ G U → MapsTo (twoJet G) U K →
      WeightedBound U s m C (twoJet G) →
      ReconstructionCoefficientBound G U s m ((m.factorial : ℝ) * D * C ^ m) := by
  obtain ⟨D, hD, hbD⟩ := smooth_compact_weighted_bound hU.uniqueDiffOn hΩ.isOpen.uniqueDiffOn
    hK hKΩ hΩ.smoothCoefficients m
  refine ⟨D, hD, ?_⟩
  intro G s C hs hC hG hGK hb
  have ht := contDiffOn_twoJet hU hG
  have hGΩ : MapsTo (twoJet G) U Ω := fun p hp => hKΩ (hGK hp)
  have hc := hbD (twoJet G) s C hs hC ht hGK hb
  have hsm : ContDiffOn ℝ ∞ (LowJet.coefficients ∘ twoJet G) U :=
    hΩ.smoothCoefficients.comp ht hGΩ
  have hn : 0 ≤ (m.factorial : ℝ) * D * C ^ m :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans hD))
      (pow_nonneg (zero_le_one.trans hC) _)
  have hscalar (i : Fin 8) := hc.component hU.uniqueDiffOn hs.le hn hsm (Sum.inl i)
  have hvector (i : Fin 5) : WeightedBound U s m ((m.factorial : ℝ) * D * C ^ m)
      (fun p => LowJet.vectorCoefficients (twoJet G p) i) := by
    apply WeightedBound.pi hU.uniqueDiffOn hs hn
    · intro a
      exact contDiffOn_pi.mp hsm (Sum.inr (i, a))
    · intro a
      exact hc.component hU.uniqueDiffOn hs.le hn hsm (Sum.inr (i, a))
  exact ⟨⟨⟨hscalar 0, hscalar 1, hscalar 2, hscalar 3, hscalar 4, hscalar 5,
    hscalar 6, hscalar 7⟩, hvector 0, hvector 1⟩, hvector 2, hvector 3, hvector 4⟩

end ClosedSurfaceR4.SmallModes

end

end OAI
