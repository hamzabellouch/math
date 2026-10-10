import OAI.Probability.GammaPassage.SurvivalRounding
import OAI.Probability.GammaPassage.BKPrimitives

namespace OAI

namespace GammaFPP.BK
open PlanarFPP Finset Set

lemma survival_le_one (t : ℕ) (x : Finset (Edge × Fin t)) (e : Edge) :
    dyadicSurvival t x e ≤ 1 := by
  rw [dyadicSurvival_eq_rank, div_le_iff₀ (by positivity), one_mul]
  exact_mod_cast (GammaFPP.dyadicRank_lt t x e).le

/-- The guard implements infinity at zero; D's totalized value at zero is unused. -/
def BitGood (D : ℝ → ℝ) (t : ℕ) (x : Finset (Edge × Fin t))
    (p : StrictPathWitness) : Prop :=
  (∀ e ∈ p.edges, 0 < dyadicSurvival t x e) ∧
    pathCost (fun e => D (dyadicSurvival t x e)) p.start p.steps < p.bound

lemma bitGood_mono {D : ℝ → ℝ} (hD : AntitoneOn D (Ioc 0 1))
    {t : ℕ} {x y : Finset (Edge × Fin t)} {p : StrictPathWitness}
    (h : BitGood D t x p) (hxy : x ⊆ y) : BitGood D t y p := by
  constructor
  · intro e he
    exact (h.1 e he).trans_le (dyadicSurvival_mono t hxy e)
  · apply lt_of_le_of_lt (pathCost_le_of_edges p.start p.steps ?_) h.2
    intro e he
    exact hD ⟨h.1 e he, survival_le_one t x e⟩
      ⟨(h.1 e he).trans_le (dyadicSurvival_mono t hxy e), survival_le_one t y e⟩
      (dyadicSurvival_mono t hxy e)

lemma bitGood_of_agree {D : ℝ → ℝ} {t : ℕ}
    {x y : Finset (Edge × Fin t)} {p : StrictPathWitness}
    (h : BitGood D t x p)
    (hxy : ∀ a ∈ p.bits t, a ∈ y ↔ a ∈ x) : BitGood D t y p := by
  have heq : ∀ e ∈ p.edges, dyadicSurvival t y e = dyadicSurvival t x e := by
    intro e he
    exact dyadicSurvival_eq t y x e (fun a => hxy (e,a) (by
      simpa only [StrictPathWitness.bits, Finset.mem_product, Finset.mem_univ, and_true] using he))
  constructor
  · intro e he
    rw [heq e he]
    exact h.1 e he
  · have hc := pathCost_eq_of_agree
      (fun e => D (dyadicSurvival t y e)) (fun e => D (dyadicSurvival t x e))
      p.start p.steps (fun e he => congrArg D (heq e he))
    rw [hc]
    exact h.2

noncomputable def bitFamily (D : ℝ → ℝ) (S : Finset Edge) (t : ℕ)
    (F : Set StrictPathWitness) : Finset (Finset (Edge × Fin t)) := by
  classical
  exact (S.product (Finset.univ : Finset (Fin t))).powerset.filter
    (fun x => ∃ p ∈ F, p.edges ⊆ S ∧ BitGood D t x p)

lemma mem_bitFamily (D : ℝ → ℝ) (S : Finset Edge) (t : ℕ)
    (F : Set StrictPathWitness) (x : Finset (Edge × Fin t)) :
    x ∈ bitFamily D S t F ↔ x ⊆ S.product (Finset.univ : Finset (Fin t)) ∧
      ∃ p ∈ F, p.edges ⊆ S ∧ BitGood D t x p := by
  classical
  simp only [bitFamily, Finset.mem_filter, Finset.mem_powerset]

lemma upward_bitFamily {D : ℝ → ℝ} (hD : AntitoneOn D (Ioc 0 1))
    (S : Finset Edge) (t : ℕ) (F : Set StrictPathWitness) :
    UpwardFamily (S.product (Finset.univ : Finset (Fin t))) (bitFamily D S t F) := by
  constructor
  · intro x hx
    exact ((mem_bitFamily ..).mp hx).1
  · intro x hx y hxy hys
    obtain ⟨_,p,hp,he,hg⟩ := (mem_bitFamily ..).mp hx
    exact (mem_bitFamily ..).mpr ⟨hys,p,hp,he,bitGood_mono hD hg hxy⟩

lemma bit_path_forces (D : ℝ → ℝ) (S : Finset Edge) (t : ℕ)
    (F : Set StrictPathWitness) (x : Finset (Edge × Fin t)) (p : StrictPathWitness)
    (hp : p ∈ F) (he : p.edges ⊆ S) (hg : BitGood D t x p) :
    ForcesBits (S.product (Finset.univ : Finset (Fin t))) (bitFamily D S t F) x (p.bits t) := by
  intro y hys hxy
  exact (mem_bitFamily ..).mpr ⟨hys,p,hp,he,bitGood_of_agree hg hxy⟩

noncomputable def bitDisjointFamily (D : ℝ → ℝ) (S : Finset Edge) (t : ℕ)
    (Fs : List (Set StrictPathWitness)) : Finset (Finset (Edge × Fin t)) := by
  classical
  exact (S.product (Finset.univ : Finset (Fin t))).powerset.filter (fun x =>
    ∃ ps : List StrictPathWitness,
      List.Forall₂ (fun p F => p ∈ F ∧ p.edges ⊆ S ∧ BitGood D t x p) ps Fs ∧
      ps.Pairwise (fun p q => Disjoint p.edges q.edges))

/-- Repeated labelled families are allowed: independence of events is not assumed. -/
theorem decoder_finite_path_BK {D : ℝ → ℝ} (hD : AntitoneOn D (Ioc 0 1))
    (S : Finset Edge) (t : ℕ) (Fs : List (Set StrictPathWitness)) :
    fairFamilyMass (S.product (Finset.univ : Finset (Fin t))) (bitDisjointFamily D S t Fs) ≤
      (Fs.map (fun F => fairFamilyMass (S.product (Finset.univ : Finset (Fin t))) (bitFamily D S t F))).prod := by
  apply (finite_fair_BK_forcing (S.product (Finset.univ : Finset (Fin t))) (Fs.map (bitFamily D S t))
    (bitDisjointFamily D S t Fs) ?_ ?_).trans_eq
      (by simp only [List.map_map,Function.comp_def])
  · intro A hA
    obtain ⟨F,_,rfl⟩ := List.mem_map.mp hA
    exact upward_bitFamily hD S t F
  · intro x hx
    simp only [bitDisjointFamily,Finset.mem_filter,Finset.mem_powerset] at hx
    obtain ⟨hxs,ps,hps,hd⟩ := hx
    refine ⟨hxs,ps.map (fun p => p.bits t),?_,?_⟩
    · clear hd
      induction hps with
      | nil => exact List.Forall₂.nil
      | cons h ht ih =>
        exact List.Forall₂.cons (bit_path_forces D S t _ x _ h.1 h.2.1 h.2.2) ih
    · rw [List.pairwise_map]
      exact hd.imp (fun h => StrictPathWitness.disjoint_bits t h)

/-- Actual Gamma decoder, for every positive shape and rate. -/
theorem gamma_decoder_finite_path_BK {shape rate : ℝ} (hs : 0 < shape) (hr : 0 < rate)
    (S : Finset Edge) (t : ℕ) (Fs : List (Set StrictPathWitness)) :
    fairFamilyMass (S.product (Finset.univ : Finset (Fin t))) (bitDisjointFamily (gammaSurvivalQuantile hs hr) S t Fs) ≤
      (Fs.map (fun F => fairFamilyMass (S.product (Finset.univ : Finset (Fin t)))
        (bitFamily (gammaSurvivalQuantile hs hr) S t F))).prod :=
  decoder_finite_path_BK (gammaSurvivalQuantile_antitoneOn hs hr) S t Fs
end GammaFPP.BK

end OAI
