import OAI.MathematicalPhysics.Heisenberg.LatticeRegularity

namespace OAI

noncomputable section

open scoped Classical BigOperators
open Module
open scoped BigOperators

open scoped Classical

open scoped BigOperators Classical
namespace Heisenberg.Exposure

section
open Heisenberg.Cycle Heisenberg.LayeredExchange
variable {T V : Type*} [Fintype T] [Fintype V]

def layerHoles (s : Equiv.Perm T) (τ : T → Equiv.Perm V)
    (P : Set (T × V)) (b : T → Bool) (t : T) : Set V :=
  {v | (t,v) ∉ MissingSet (layerHistory s τ b) P}

omit [Fintype T] [Fintype V] in
lemma layerHoles_pin (s : Equiv.Perm T) (τ : T → Equiv.Perm V)
    (P : Set (T × V)) (b : T → Bool) (t : T) (v : V) (hv : (t,v) ∈ P) :
    v ∈ layerHoles s τ P b t := by
  intro h
  exact h (t,v) hv rfl

omit [Fintype T] [Fintype V] in
lemma layerHoles_transport (s : Equiv.Perm T) (τ : T → Equiv.Perm V)
    (P : Set (T × V)) (b : T → Bool) (t : T) (v : V) :
    (if b t then τ t else 1) v ∈ layerHoles s τ P b (s t) ↔
      v ∈ layerHoles s τ P b t := by
  exact not_congr (missing_apply (layerHistory s τ b) P (t,v))

omit [Fintype T] [Fintype V] in
lemma layerHoles_quiet (s : Equiv.Perm T) (τ : T → Equiv.Perm V)
    (P : Set (T × V)) (b : T → Bool) (t : T) (hb : b t = false) :
    layerHoles s τ P b (s t) = layerHoles s τ P b t := by
  ext v
  simpa only [hb,Bool.false_eq_true,ite_false,Equiv.Perm.one_apply] using
    layerHoles_transport s τ P b t v

omit [Fintype T] [Fintype V] in
lemma swap_layerRevealed [DecidableEq V] (a b : T → V) (hab : ∀ t,a t ≠ b t)
    (A : Set (T × V)) (t : T) :
    layerRevealed (fun t => Equiv.swap (a t) (b t)) A t ↔
      (t,a t) ∈ A ∨ (t,b t) ∈ A := by
  constructor
  · rintro ⟨v,hv,hne⟩
    by_cases hva : v=a t
    · exact Or.inl (hva ▸ hv)
    by_cases hvb : v=b t
    · exact Or.inr (hvb ▸ hv)
    exact False.elim (hne (Equiv.swap_apply_of_ne_of_ne hva hvb))
  · rintro (ha | hb)
    · exact ⟨a t,ha,by simpa using (hab t).symm⟩
    · exact ⟨b t,hb,by simpa using hab t⟩

def layerBlocked {X : Type*} (loc : V → X) (s : Equiv.Perm T)
    (τ : T → Equiv.Perm V) (P : Set (T × V)) (b : T → Bool) (t : T) : Set X :=
  {x | (∃ v,loc v=x) ∧ ∀ v,loc v=x → v ∉ layerHoles s τ P b t}

omit [Fintype T] in
lemma layerBlocked_finite {X : Type*} (loc : V → X) (s : Equiv.Perm T)
    (τ : T → Equiv.Perm V) (P : Set (T × V)) (b : T → Bool) (t : T) :
    (layerBlocked loc s τ P b t).Finite :=
  (Set.finite_range loc).subset fun _ h => h.1

omit [Fintype T] [Fintype V] in
lemma layerBlocked_pin {X : Type*} (loc : V → X) (s : Equiv.Perm T)
    (τ : T → Equiv.Perm V) (P : Set (T × V)) (b : T → Bool) (t : T) (v : V)
    (hv : (t,v) ∈ P) : loc v ∉ layerBlocked loc s τ P b t := by
  intro h
  exact h.2 v rfl (layerHoles_pin s τ P b t v hv)

def localGrowth {X Y : Type*} [PseudoMetricSpace X] (loc : Y → X)
    (α L : ℝ) (U : Finset Y) : Prop :=
  ∀ (x : X) (h : ℝ), 0 ≤ h →
    ((U.filter (fun v => dist (loc v) x ≤ h)).card : ℝ) ≤ L*(1+h)^α

omit [Fintype T] [Fintype V] in
lemma localGrowth_image {X Y Z : Type*} [PseudoMetricSpace X] [DecidableEq Z]
    (loc : Z → X) (f : Y → Z) (F : Finset Y) (α L : ℝ)
    (hf : Function.Injective f) :
    localGrowth loc α L (F.image f) ↔ localGrowth (loc ∘ f) α L F := by
  unfold localGrowth
  have he (x : X) (r : ℝ) :
      ((F.image f).filter (fun v => dist (loc v) x ≤ r)).card =
        (F.filter (fun v => dist (loc (f v)) x ≤ r)).card := by
    rw [Finset.filter_image]
    exact Finset.card_image_of_injective _ hf
  simp only [he,Function.comp_apply]

theorem layer_blocked_mass_le {X : Type*} [PseudoMetricSpace X]
    (loc : V → X) (s : Equiv.Perm T) (τ : T → Equiv.Perm V)
    (P : Set (T × V)) (t : T) (μ : (T → Bool) → ℝ) (hμ : ∀ b,0≤μ b)
    (α L p : ℝ) (hp : 0≤p)
    (htest : ∀ U : Finset V, localGrowth loc α L U →
      (∀ v ∈ U,(t,v) ∉ P) →
      (∑ b,if ∀ v ∈ U,(t,v) ∈ MissingSet (layerHistory s τ b) P then μ b else 0) ≤ p^U.card)
    (F : Finset X) (hF : localGrowth id α L F) :
    (∑ b,if (F:Set X) ⊆ layerBlocked loc s τ P b t then μ b else 0) ≤ p^F.card := by
  classical
  by_cases hr : ∀ x ∈ F,∃ v,loc v=x
  · choose r hloc using (fun x : F => hr x x.property)
    let U : Finset V := Finset.univ.image r
    have hinj : Function.Injective r := by
      intro x y h
      apply Subtype.ext
      exact (hloc x).symm.trans ((congrArg loc h).trans (hloc y))
    have hcard : U.card=F.card := by
      rw [Finset.card_image_of_injective _ hinj,Finset.card_univ,Fintype.card_coe]
    have hUg : localGrowth loc α L U := by
      rw [localGrowth_image _ _ _ _ _ hinj]
      intro x h hh
      have he : (Finset.univ.filter (fun v : F => dist (loc (r v)) x ≤ h)).card =
          (F.filter (fun v => dist v x ≤ h)).card := by
        simp only [hloc]
        apply Finset.card_bij (fun v _ => v.val)
        · intro v hv
          exact Finset.mem_filter.mpr ⟨v.property,(Finset.mem_filter.mp hv).2⟩
        · intro v _ w _ h
          exact Subtype.ext h
        · intro v hv
          exact ⟨⟨v,(Finset.mem_filter.mp hv).1⟩,by simpa using (Finset.mem_filter.mp hv).2,rfl⟩
      simpa only [Function.comp_apply,he,id_eq] using hF x h hh
    have hcover (b) (hb : (F:Set X) ⊆ layerBlocked loc s τ P b t) :
        ∀ v ∈ U,(t,v) ∈ MissingSet (layerHistory s τ b) P := by
      intro v hv
      obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hv
      exact not_not.mp ((hb x.property).2 (r x) (hloc x))
    by_cases hP : ∀ v ∈ U,(t,v) ∉ P
    · calc
        _ ≤ ∑ b,if ∀ v ∈ U,(t,v) ∈ MissingSet (layerHistory s τ b) P then μ b else 0 := by
          apply Finset.sum_le_sum
          intro b _
          split_ifs with hb hm
          · rfl
          · exact False.elim (hm (hcover b hb))
          · exact hμ b
          · rfl
        _ ≤ p^U.card := htest U hUg hP
        _ = _ := by rw [hcard]
    · have hz : ∀ b,¬(F:Set X) ⊆ layerBlocked loc s τ P b t := by
        intro b hb
        obtain ⟨v,hv,hvP⟩ := by simpa only [not_forall,Classical.not_imp,not_not] using hP
        exact hcover b hb v hv (t,v) hvP rfl
      simp only [hz,ite_false,Finset.sum_const_zero]
      exact pow_nonneg hp _
  · have hz : ∀ b,¬(F:Set X) ⊆ layerBlocked loc s τ P b t := by
      intro b hb
      exact hr fun x hx => (hb hx).1
    simp only [hz,ite_false,Finset.sum_const_zero]
    exact pow_nonneg hp _

end

open Heisenberg.Geometry Heisenberg.SparseWitness Heisenberg.LatticeRegular
variable {T V : Type*} [Fintype T] [Fintype V]

theorem layer_regularity (k M b : ℕ) (hb : 100≤b)
    (α L ν a : ℝ) (hα : 0≤α) (hL : (2*(k+1):ℕ)≤L)
    (hba : 2≤(b:ℝ)^α) (hν : 0<ν) (ha : 0≤a) :
    ∃ p₀>0,∃ C≥0,∀ (loc : V → Site (k+1)) (s : Equiv.Perm T)
      (u v : T → V) (P : Set (T×V)) (rates : T → ℝ)
      (_hrates : ∀ i,0≤rates i ∧ rates i≤1) (t : T) (p : ℝ),
      0≤p → p≤p₀ →
      (∀ U : Finset V,localGrowth loc α L U → (∀ j∈U,(t,j)∉P) →
        (∑ c,if ∀ j∈U,(t,j)∈Cycle.MissingSet
          (layerHistory s (fun i=>Equiv.swap (u i) (v i)) c) P then
          layerMass s u v P rates c else 0)≤p^U.card) →
      ∀ (x : Site (k+1)) (R : ℕ),
        (∑ c,if ¬Regular (layerBlocked loc s (fun i=>Equiv.swap (u i) (v i)) P c t)
          x R M ν then layerMass s u v P rates c else 0) ≤
          C*((1+(R:ℝ))^(k+1)*p^(2*(k+1))+(1+(R:ℝ))^(-a)) := by
  obtain ⟨p₀,hp₀,C,hC,hr⟩ := regularity_probability k M b hb α L ν a hα hL hba hν ha
  refine ⟨p₀,hp₀,C,hC,?_⟩
  intro loc s u v P rates hrates t p hp hpp htest x R
  apply hr (T → Bool) (layerMass s u v P rates)
    (fun c=>layerBlocked loc s (fun i=>Equiv.swap (u i) (v i)) P c t) p
    (layerMass_nonneg s u v P rates hrates) (layerMass_sum s u v P rates hrates).le hp hpp _ x R
  intro F hF
  exact layer_blocked_mass_le loc s (fun i=>Equiv.swap (u i) (v i)) P t
    (layerMass s u v P rates) (layerMass_nonneg s u v P rates hrates)
    α L p hp htest F hF

end Heisenberg.Exposure

end

end OAI
