import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.FacePoint

namespace OAI

namespace MetricKMedianRecovery.RationalLinearFeasibility
open scoped BigOperators
variable {V R : Type*} [Fintype V] {n : ℕ}

def ellipsoidForms (e : Fin n ≃ V) (rows : List R) (f : R → Form V) (B : ℕ) :
    Option (V → ℚ) :=
  (Ellipsoid.exactSolve (rows.map (fun r => (f r).enumeratedRow e)) B).map
    (fun y v => y (e.symm v))

lemma ellipsoidForms_sound (e : Fin n ≃ V) (rows : List R) (f : R → Form V) (B : ℕ)
    (x : V → ℚ) (hx : ellipsoidForms e rows f B=some x) :
    (∀ r∈rows,(f r).eval x≤0) ∧ (∀ j,|x j|≤(B:ℚ)) := by
  obtain ⟨y,hy,rfl⟩ := Option.map_eq_some_iff.mp hx
  have hs := Ellipsoid.exactSolve_some _ B y hy
  exact ⟨fun r hr => ((f r).enumeratedRow_holds e y).mp
    (hs.1 _ (List.mem_map.mpr ⟨r,hr,rfl⟩)),fun j => hs.2 (e.symm j)⟩

lemma ellipsoidForms_complete (e : Fin n ≃ V) (rows : List R) (f : R → Form V) (B : ℕ)
    (x : V → ℝ) (hx : ∀ r∈rows,(f r).realEval x≤0) (hb : ∀ j,|x j|≤(B:ℝ)) :
    ∃ y,ellipsoidForms e rows f B=some y := by
  have hh : ∀ q∈rows.map (fun r => (f r).enumeratedRow e),q.RealHolds (fun i => x (e i)) := by
    intro q hq
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hq
    exact ((f r).enumeratedRow_realHolds e x).mpr (hx r hr)
  obtain ⟨y,hy⟩ := Ellipsoid.exactSolve_complete _ B ⟨fun i => x (e i),hh,fun i => hb (e i)⟩
  exact ⟨fun v => y (e.symm v),by simp only [ellipsoidForms,hy,Option.map_some]⟩

end MetricKMedianRecovery.RationalLinearFeasibility

namespace MetricKMedianRecovery.EffectiveOpenability
open RationalLinearFeasibility RationalOpenability OpenabilityLinearization

def ellipsoidOpening {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z lam eta : ℚ) (i : Fin m) : Option (Variables (Fin d) F → ℚ) :=
  ellipsoidForms (variableEnum d F)
    (kindRows (List.ofFn (fun j : Fin d => j)) (subtypeList W) (subtypeList F))
    (forms distance F W v z lam eta i) ⌈(1+v^2)*z⌉₊

lemma ellipsoidOpening_witness {m d : ℕ} [PseudoMetricSpace (Fin m)]
    (loc : Fin d → Fin m) (distance : Fin m → Fin d → ℚ)
    (hd : ∀ f j,(distance f j:ℝ)=dist f (loc j))
    (F W : Finset (Fin m)) (v z lam eta : ℚ) (i : Fin m)
    (x : Variables (Fin d) F → ℚ) (hx : ellipsoidOpening distance F W v z lam eta i=some x) :
    Feasible loc F W (v:ℝ) (z:ℝ) (lam:ℝ) (eta:ℝ) i
      (fun j => (x (.inl j):ℝ)) (fun f a j => (x (.inr (f,a,j)):ℝ)) := by
  have hs := (ellipsoidForms_sound _ _ _ _ x hx).1
  apply (system_iff loc distance hd F W v z lam eta i (fun j => (x j:ℝ))).mp
  intro k
  rw [←forms_eq loc distance hd,Form.realEval_cast]
  exact_mod_cast hs k (mem_kindRows _ _ _ (by simp) (mem_subtypeList W) (mem_subtypeList F) k)

lemma ellipsoidOpening_sound {m d : ℕ} [PseudoMetricSpace (Fin m)]
    (loc : Fin d → Fin m) (distance : Fin m → Fin d → ℚ)
    (hd : ∀ f j,(distance f j:ℝ)=dist f (loc j))
    (F W : Finset (Fin m)) (v z lam eta : ℚ) (i : Fin m)
    (hv : (0:ℝ)<(v:ℝ)) (hv1 : (v:ℝ)<1/6) (hz : (0:ℝ)≤(z:ℝ))
    (x : Variables (Fin d) F → ℚ) (hx : ellipsoidOpening distance F W v z lam eta i=some x) :
    etaOpenable loc F W (1-3*(v:ℝ)) (1+(v:ℝ)^2) (v:ℝ) (z:ℝ) (lam:ℝ) (eta:ℝ) i := by
  apply (openable_iff_linear_feasible loc F W (v:ℝ) (z:ℝ) (lam:ℝ) (eta:ℝ) i hv hv1 hz).mpr
  exact ⟨_,_,ellipsoidOpening_witness loc distance hd F W v z lam eta i x hx⟩

lemma ellipsoidOpening_complete {m d : ℕ} [PseudoMetricSpace (Fin m)]
    (loc : Fin d → Fin m) (distance : Fin m → Fin d → ℚ)
    (hd : ∀ f j,(distance f j:ℝ)=dist f (loc j))
    (F W : Finset (Fin m)) (v z lam eta : ℚ) (i : Fin m)
    (hv : (0:ℝ)<(v:ℝ)) (hv1 : (v:ℝ)<1/6) (hz : (0:ℝ)≤(z:ℝ))
    (h : etaOpenable loc F W (1-3*(v:ℝ)) (1+(v:ℝ)^2) (v:ℝ) (z:ℝ) (lam:ℝ) (eta:ℝ) i) :
    ∃ x,ellipsoidOpening distance F W v z lam eta i=some x := by
  obtain ⟨tau,y,hf,ht,hy⟩ := (openable_iff_bounded loc F W (v:ℝ) (z:ℝ) (lam:ℝ) (eta:ℝ) i hv hv1 hz).mp h
  let x : Variables (Fin d) F → ℝ := Sum.elim tau (fun p => y p.1 p.2.1 p.2.2)
  have hx : ∀ k,(forms distance F W v z lam eta i k).realEval x≤0 := by
    rw [forms_eq loc distance hd]
    exact (system_iff loc distance hd F W v z lam eta i x).mpr hf
  have hb : ∀ j,|x j|≤(⌈(1+v^2)*z⌉₊:ℝ) := by
    intro j
    have hh : 0≤x j ∧ x j≤(1+(v:ℝ)^2)*(z:ℝ) := by
      cases j with
      | inl j => exact ht j
      | inr p => exact hy p.1 p.2.1 p.2.2
    rw [abs_of_nonneg hh.1]
    apply hh.2.trans
    have hb := Nat.le_ceil ((1+v^2)*z)
    exact_mod_cast hb
  exact ellipsoidForms_complete _ _ _ _ x (fun k _ => hx k) hb

lemma ellipsoidOpening_none_iff {m d : ℕ} [PseudoMetricSpace (Fin m)]
    (loc : Fin d → Fin m) (distance : Fin m → Fin d → ℚ)
    (hd : ∀ f j,(distance f j:ℝ)=dist f (loc j))
    (F W : Finset (Fin m)) (v z lam eta : ℚ) (i : Fin m)
    (hv : (0:ℝ)<(v:ℝ)) (hv1 : (v:ℝ)<1/6) (hz : (0:ℝ)≤(z:ℝ)) :
    ellipsoidOpening distance F W v z lam eta i=none ↔
      ¬etaOpenable loc F W (1-3*(v:ℝ)) (1+(v:ℝ)^2) (v:ℝ) (z:ℝ) (lam:ℝ) (eta:ℝ) i := by
  constructor
  · intro hn ho
    obtain ⟨x,hx⟩ := ellipsoidOpening_complete loc distance hd F W v z lam eta i hv hv1 hz ho
    simp [hn] at hx
  · intro hn
    cases he : ellipsoidOpening distance F W v z lam eta i with
    | none => rfl
    | some x => exact (hn (ellipsoidOpening_sound loc distance hd F W v z lam eta i hv hv1 hz x he)).elim

end MetricKMedianRecovery.EffectiveOpenability

end OAI
