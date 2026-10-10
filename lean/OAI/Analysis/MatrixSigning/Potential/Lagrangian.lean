import Mathlib
import OAI.Analysis.MatrixSigning.Potential.PairCone
import OAI.Analysis.MatrixSigning.Potential.StrictEpigraph

namespace OAI

open Matrix

namespace CurrentKS.Variational
noncomputable section
open CurrentKS.Hermitian Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

lemma convex_domain : Convex ℝ (domain d) := by
  intro z hz w hw a b ha hb hab
  exact ⟨convex_pd hz.1 hw.1 ha hb hab, convex_pd hz.2 hw.2 ha hb hab⟩

lemma convex_objective (ε : ℝ) : ConvexOn ℝ (domain d) (objective ε) := by
  refine ⟨convex_domain, ?_⟩
  intro z hz w hw a b ha hb hab
  apply le_of_eq
  simp only [objective, Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd,
    realTrace_add, realTrace_smul, smul_eq_mul]
  ring

lemma residual_coneConvex (S : H d) (η : H d →L[ℝ] H d)
    (z : Point d) (hz : z ∈ domain d) (w : Point d) (hw : w ∈ domain d)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    a • residual S η z + b • residual S η w - residual S η (a • z + b • w) ∈ pairCone d := by
  have hX := inverse_convex hz.1 hw.1 ha hb hab
  have hY := inverse_convex hz.2 hw.2 ha hb hab
  have he : a • residual S η z + b • residual S η w - residual S η (a • z + b • w) =
      (a • invH z.2.1 + b • invH w.2.1 - invH (a • z.2.1 + b • w.2.1),
        a • invH z.2.2 + b • invH w.2.2 - invH (a • z.2.2 + b • w.2.2)) +
      ((a+b-1) • S, -(a+b-1) • S) := by
    apply Prod.ext <;> simp only [residual, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
      Prod.smul_fst, Prod.smul_snd, map_add, map_smul, smul_eq_mul] <;> module
  rw [he, hab]
  simpa using And.intro hX hY

lemma unit_le_slack {R : H d} {r : ℝ} (hR : R ≤ r • (Hermitian.one : H d)) :
    (Hermitian.one : H d) ≤ (r+1) • (Hermitian.one : H d) - R := by
  have hh := sub_le_sub_left hR ((r+1) • (Hermitian.one : H d))
  convert hh using 1
  module

lemma invH_one : invH (Hermitian.one : H d) = Hermitian.one := by
  apply Subtype.ext
  simp [invH]

lemma exists_strict_feasible [NeZero d] (S : H d) (η : H d →L[ℝ] H d)
    (hη : ∀ A ∈ psdCone d, η A ∈ psdCone d)
    {K : ℝ} (hS₁ : -K • (Hermitian.one : H d) ≤ S) (hS₂ : S ≤ K • (Hermitian.one : H d)) :
    ∃ z ∈ domain d, -residual S η z ∈ interior (pairCone d : Set (H d × H d)) := by
  let I : H d := Hermitian.one
  let t : ℝ := K + realTrace (η I) + 2
  let z : Point d := (t,I,I)
  have heη : η I ≤ realTrace (η I) • I := trace_bound_above (hη I one_mem_psdCone)
  have hmS : -S ≤ K • I := by
    have hh := neg_le_neg hS₁
    have he : -((-K) • (Hermitian.one : H d)) = K • I := by module
    rw [he] at hh
    exact hh
  have hR₁ : I + S + η I ≤ (1+K+realTrace (η I)) • I := by
    have hh := add_le_add_left (add_le_add hS₂ heη) I
    convert hh using 1 <;> first | rfl | module
  have hR₂ : I - S + η I ≤ (1+K+realTrace (η I)) • I := by
    have hh := add_le_add_left (add_le_add hmS heη) I
    convert hh using 1 <;> first | rfl | module
  have hs₁ : (-residual S η z).1 ∈ pd d := by
    apply pd_of_lower (a := 1) zero_lt_one
    have hh := unit_le_slack hR₁
    dsimp [residual, z, t]
    rw [show invH I = I from invH_one]
    convert hh using 1 <;> first | rfl | module
  have hs₂ : (-residual S η z).2 ∈ pd d := by
    apply pd_of_lower (a := 1) zero_lt_one
    have hh := unit_le_slack hR₂
    dsimp [residual, z, t]
    rw [show invH I = I from invH_one]
    convert hh using 1 <;> first | rfl | module
  refine ⟨z, ⟨Matrix.PosDef.one, Matrix.PosDef.one⟩, ?_⟩
  change -residual S η z ∈ interior ((psdCone d : Set (H d)) ×ˢ (psdCone d : Set (H d)))
  rw [interior_prod_eq]
  exact ⟨posDef_mem_interior _ hs₁, posDef_mem_interior _ hs₂⟩

def lagrangian (ε : ℝ) (S : H d) (η : H d →L[ℝ] H d) (P Q : H d) (z : Point d) : ℝ :=
  objective ε z + inner ℝ P (residual S η z).1 + inner ℝ Q (residual S η z).2

theorem exists_matrix_multipliers [NeZero d] (S : H d) (η : H d →L[ℝ] H d)
    (hη : ∀ A ∈ psdCone d, η A ∈ psdCone d)
    {ε K : ℝ} (hS₁ : -K • (Hermitian.one : H d) ≤ S) (hS₂ : S ≤ K • (Hermitian.one : H d))
    (z : Point d) (hz : z ∈ feasible S η)
    (hmin : ∀ w ∈ feasible S η, objective ε z ≤ objective ε w) :
    ∃ P Q : H d, P ∈ psdCone d ∧ Q ∈ psdCone d ∧
      inner ℝ P (residual S η z).1 + inner ℝ Q (residual S η z).2 = 0 ∧
      ∀ w ∈ domain d, lagrangian ε S η P Q z ≤ lagrangian ε S η P Q w := by
  obtain ⟨zs, hzs, hs⟩ := exists_strict_feasible S η hη hS₁ hS₂
  have hzc := (feasible_iff_cone S η z).mp hz
  obtain ⟨p, hp, hc, hl⟩ := Conic.multiplier_rule (pairCone d)
    ⟨zero_mem_psdCone, zero_mem_psdCone⟩ (domain d) (residual S η) (objective ε)
    convex_domain (convex_objective ε) (residual_coneConvex S η)
    z hzc.1 hzc.2 (fun w hw hf => hmin w ((feasible_iff_cone S η w).mpr ⟨hw,hf⟩))
    zs hzs hs
  let p₁ : StrongDual ℝ (H d) := p.comp (ContinuousLinearMap.inl ℝ (H d) (H d))
  let p₂ : StrongDual ℝ (H d) := p.comp (ContinuousLinearMap.inr ℝ (H d) (H d))
  obtain ⟨P, hP, heP⟩ := positive_dual_matrix p₁ (fun A hA => hp (A,0) ⟨hA, zero_mem_psdCone⟩)
  obtain ⟨Q, hQ, heQ⟩ := positive_dual_matrix p₂ (fun A hA => hp (0,A) ⟨zero_mem_psdCone, hA⟩)
  have he (A B : H d) : p (A,B) = inner ℝ P A + inner ℝ Q B := by
    rw [← heP, ← heQ]
    change p (A,B) = p (A,0) + p (0,B)
    rw [← map_add]
    congr 1
    simp
  have hcomp : inner ℝ P (residual S η z).1 + inner ℝ Q (residual S η z).2 = 0 := by
    rw [← he]
    exact hc
  refine ⟨P,Q,hP,hQ,hcomp, fun w hw => ?_⟩
  have h := hl w hw
  rw [show residual S η w = ((residual S η w).1,(residual S η w).2) from rfl, he] at h
  change objective ε z + inner ℝ P (residual S η z).1 + inner ℝ Q (residual S η z).2 ≤
    objective ε w + inner ℝ P (residual S η w).1 + inner ℝ Q (residual S η w).2
  linarith

end
end CurrentKS.Variational

end OAI
