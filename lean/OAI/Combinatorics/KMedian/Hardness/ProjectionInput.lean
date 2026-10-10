import Mathlib
import OAI.Combinatorics.KMedian.Hardness.Constants
import OAI.Combinatorics.KMedian.Hardness.Coverage
import OAI.Combinatorics.KMedian.Hardness.Projection
import OAI.Combinatorics.KMedian.Hardness.Sampling

namespace OAI

section Inline_PCPInherited

namespace MetricKMedian.Coverage
open Finset

namespace ProjectionSystem
variable {U V I A B : Type} [Fintype U] [Fintype V] [Fintype I]
  [Fintype A] [Fintype B] [DecidableEq U] [DecidableEq V] [DecidableEq I]
  [DecidableEq A] [DecidableEq B]
omit [Fintype U] [DecidableEq V] in
theorem covered_iff (H : ProjectionSystem U V I A B) (S : Finset (U × A))
    (v : V) (w : B → I) :
    (v,w) ∈ H.covered S ↔ ∃ i c, (H.neighbor v i,c) ∈ S ∧ w (H.project v i c) = i := by
  simp only [covered,mem_filter,mem_univ,true_and]
end ProjectionSystem

structure ProjectionInput (r a b : ℕ) where
  u : ℕ
  v : ℕ
  u_pos : 0 < u
  v_pos : 0 < v
  r_pos : 0 < r
  a_pos : 0 < a
  b_pos : 0 < b
  system : ProjectionSystem (Fin u) (Fin v) (Fin r) (Fin a) (Fin b)
  degree : ℕ
  regular : system.LeftRegular degree
  consistent : system.DuplicateConsistent

namespace ProjectionInput
variable {r a b : ℕ} (G : ProjectionInput r a b)

def Perfect : Prop := ∃ (left : Fin G.u → Fin a) (right : Fin G.v → Fin b), ∀ v i,
  G.system.project v i (left (G.system.neighbor v i)) = right v

def Sound (ε : ℝ) : Prop := ∀ left right,
  ((G.system.satisfied left right).card : ℝ) ≤ ε * G.v * r

abbrev Block (r b D : ℕ) := (Fin D → Fin r) × (Fin b → Fin D)
def width (r b D : ℕ) : ℕ := r^D * D^b

noncomputable def blockEquiv (r b D : ℕ) : Block r b D ≃ Fin (width r b D) :=
  (Fintype.equivFin _).trans (finCongr (by simp [Block,width]))

noncomputable def clientEquiv (D : ℕ) :
    ((Fin G.v × (Fin D → Fin r)) × (Fin b → Fin D)) ≃ Fin (G.v * width r b D) :=
  (Equiv.prodAssoc _ _ _).trans
    ((Equiv.prodCongr (Equiv.refl _) (blockEquiv r b D)).trans finProdFinEquiv)

abbrev facilityEquiv : (Fin G.u × Fin a) ≃ Fin (G.u * a) := finProdFinEquiv

noncomputable abbrev toCoverage (D : ℕ) (hD : 0 < D) : Input where
  m := G.v * width r b D
  n := G.u * a
  k := G.u
  m_pos := Nat.mul_pos G.v_pos (Nat.mul_pos (pow_pos G.r_pos _) (pow_pos hD _))
  k_pos := G.u_pos
  k_le := Nat.le_mul_of_pos_right _ G.a_pos
  incident x y :=
    let p := (G.clientEquiv D).symm x
    let q := G.facilityEquiv.symm y
    decide (∃ j : Fin D, G.system.neighbor p.1.1 (p.1.2 j) = q.1 ∧
      p.2 (G.system.project p.1.1 (p.1.2 j) q.2) = j)

@[simp] theorem incident_equiv (D : ℕ) (hD : 0 < D)
    (p : (Fin G.v × (Fin D → Fin r)) × (Fin b → Fin D))
    (q : Fin G.u × Fin a) :
    (G.toCoverage D hD).incident (G.clientEquiv D p) (G.facilityEquiv q) = true ↔
      ∃ j : Fin D, G.system.neighbor p.1.1 (p.1.2 j) = q.1 ∧
        p.2 (G.system.project p.1.1 (p.1.2 j) q.2) = j := by
  simp

theorem covered_equiv (D : ℕ) (hD : 0 < D) (S : Finset (Fin G.u × Fin a)) :
    (G.toCoverage D hD).covered (S.image G.facilityEquiv) =
      ((G.system.sample (Fin D)).covered S).image (G.clientEquiv D) := by
  classical
  ext x
  obtain ⟨p,rfl⟩ := (G.clientEquiv D).surjective x
  constructor
  · intro hx
    obtain ⟨y,hy,hin⟩ := ((G.toCoverage D hD).mem_covered _ _).mp hx
    obtain ⟨q,hq,rfl⟩ := mem_image.mp hy
    obtain ⟨j,hj,hw⟩ := (G.incident_equiv D hD p q).mp hin
    apply mem_image.mpr
    refine ⟨p,?_,rfl⟩
    apply ((G.system.sample (Fin D)).covered_iff S p.1 p.2).mpr
    refine ⟨j,q.2,?_,hw⟩
    change (G.system.neighbor p.1.1 (p.1.2 j),q.2) ∈ S
    simpa only [hj] using hq
  · intro hx
    obtain ⟨p',hp',he⟩ := mem_image.mp hx
    have hp : p' = p := (G.clientEquiv D).injective he
    subst p'
    obtain ⟨j,c,hc,hw⟩ := (show ∃ j c,
      (G.system.neighbor p.1.1 (p.1.2 j),c) ∈ S ∧
      p.2 (G.system.project p.1.1 (p.1.2 j) c) = j by
      exact ((G.system.sample (Fin D)).covered_iff S p.1 p.2).mp hp')
    apply ((G.toCoverage D hD).mem_covered _ _).mpr
    refine ⟨G.facilityEquiv (G.system.neighbor p.1.1 (p.1.2 j),c),
      mem_image.mpr ⟨_,hc,rfl⟩,?_⟩
    exact (G.incident_equiv D hD p _).mpr ⟨j,rfl,hw⟩

theorem coverage_perfect (D : ℕ) (hD : 0 < D) (h : G.Perfect) :
    (G.toCoverage D hD).Perfect := by
  classical
  obtain ⟨left,right,hh⟩ := h
  obtain ⟨S,hs,hcover⟩ := G.system.sample_perfect (Fin D) left right hh
  refine ⟨S.image G.facilityEquiv,?_,?_⟩
  · simpa only [card_image_of_injective _ G.facilityEquiv.injective,
      toCoverage,Fintype.card_fin] using hs
  · rw [G.covered_equiv D hD,hcover]
    exact image_univ_of_surjective (G.clientEquiv D).surjective

theorem coverage_sound {δ : ℝ} (P : PartitionParameters δ) (h : G.Sound P.ε) :
    (G.toCoverage P.D (by have := P.D_ge; omega)).Sound δ := by
  classical
  let : Nonempty (Fin b) := ⟨⟨0,G.b_pos⟩⟩
  intro T hT
  let S := T.image G.facilityEquiv.symm
  have hS : S.card ≤ Fintype.card (Fin G.u) := by
    simpa only [S,card_image_of_injective _ G.facilityEquiv.symm.injective,
      Fintype.card_fin,toCoverage] using hT
  have he : S.image G.facilityEquiv = T := by
    simp only [S,image_image,Function.comp_def,Equiv.apply_symm_apply,image_id']
  have hc := G.system.sampled_coverage_bound (Fin P.D) G.regular G.consistent
    (by simp only [Fintype.card_fin]; have := P.D_ge; omega) S hS P.t_pos ⟨0,G.a_pos⟩
    (P.ε : ℝ) (by simpa only [Sound,Fintype.card_fin] using h)
  have hcard : ((G.toCoverage P.D _).covered T).card =
      ((G.system.sample (Fin P.D)).covered S).card := by
    rw [← he,G.covered_equiv]
    exact card_image_of_injective _ (G.clientEquiv P.D).injective
  rw [hcard]
  have hmargin := le_of_lt P.margin
  have hw : (0 : ℝ) ≤ (G.v : ℝ) * (r : ℝ)^P.D * (P.D : ℝ)^b := by positivity
  have hmul := mul_le_mul_of_nonneg_right hmargin hw
  simp only [Fintype.card_fin,Fintype.card_prod,Fintype.card_fun,Nat.cast_mul,
    Nat.cast_pow] at hc
  change _ ≤ (1 - 1 / Real.exp 1 + δ) * ((G.v * width r b P.D : ℕ) : ℝ)
  simp only [width,Nat.cast_mul,Nat.cast_pow]
  nlinarith [hc,hmul]

end ProjectionInput
end MetricKMedian.Coverage

end Inline_PCPInherited

end OAI
