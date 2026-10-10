import OAI.Geometry.PlaneColoring.AngularBoundary

namespace OAI

noncomputable section
open Set
namespace EuclideanFiveColor
def fiveDiag (i : Fin 5) : Finset (Fin 5) := {i,i+2}
def fiveAdj (i j : Fin 5) : Prop := i+1=j ∨ j+1=i
instance (i j : Fin 5) : Decidable (fiveAdj i j) := inferInstanceAs (Decidable (_ ∨ _))
def fiveEdge (i : Fin 5) : Finset (Fin 5) := {i,i+1}
def FiveAdmissible (p : Finset (Fin 5)) : Prop :=
  p.Nonempty ∧ p.card≤2 ∧ ∀ i : Fin 5, ¬p⊆fiveEdge i
def fiveCanonical (p : Finset (Fin 5)) : Fin 5 :=
  if p=fiveDiag 0 then 0 else if p=fiveDiag 1 then 1 else if p=fiveDiag 2 then 2 else
    if p=fiveDiag 3 then 3 else 4
lemma five_admissible_diag : ∀p : Finset (Fin 5), FiveAdmissible p → p=fiveDiag (fiveCanonical p) := by
  unfold FiveAdmissible
  decide
lemma five_diag_disjoint : ∀i j : Fin 5, Disjoint (fiveDiag i) (fiveDiag j) ↔ fiveAdj i j := by decide
lemma five_diag_nonempty (i : Fin 5) : (fiveDiag i).Nonempty := ⟨i,Finset.mem_insert_self _ _⟩
lemma five_diag_unique : ∀i j : Fin 5, fiveDiag i=fiveDiag j → i=j := by decide
lemma five_adj_four : ∀i j : Fin 5, fiveAdj i j → ∃ X : Fin 5, ∀k, k∉fiveDiag i∪fiveDiag j ↔ k=X := by decide
lemma five_no_common_adj : ∀I : Finset (Fin 5), I.Nonempty → (∀k,∃i∈I,k∉fiveDiag i) →
    ∃i∈I,∃j∈I,fiveAdj i j := by decide
lemma five_forced_label : ∀i j X : Fin 5, fiveAdj i j →
    (∀k,k∉fiveDiag i∪fiveDiag j ↔ k=X) → ∀p : Finset (Fin 5),
    Disjoint p (fiveDiag i) → ¬p⊆fiveDiag j → X∈p := by decide
end EuclideanFiveColor
end

noncomputable section
namespace EuclideanFiveColor
/-- Labels allowed on the side selected by `b`; a label survives precisely when
both of its incident edges have the opposite sign. -/
def sideAllowed (s : Fin 5 → Bool) (b : Bool) : Finset (Fin 5) :=
  Finset.univ.filter fun i => s (i-1)≠b ∧ s i≠b
/-- Both actual one-sided strip restrictions on a palette. -/
def SideCompatible (s : Fin 5 → Bool) (p : Finset (Fin 5)) : Prop :=
  p.card≤2 ∧ (p∩sideAllowed s true).Nonempty ∧ (p∩sideAllowed s false).Nonempty
instance (s : Fin 5 → Bool) (p : Finset (Fin 5)) : Decidable (SideCompatible s p) :=
  inferInstanceAs (Decidable (_∧_∧_))
lemma side_compatible_diagonal : ∀s : Fin 5 → Bool,∀p : Finset (Fin 5),
    SideCompatible s p → p=fiveDiag (fiveCanonical p) := by decide
lemma side_compatible_options : ∀s : Fin 5 → Bool,∀i j : Fin 5,
    SideCompatible s (fiveDiag i) → SideCompatible s (fiveDiag j) →
    j=i ∨ j=i+2 ∨ j=i-2 := by decide
lemma side_allowed_not (s : Fin 5 → Bool) (b : Bool) :
    sideAllowed (fun i => !(s i)) b=sideAllowed s (!b) := by
  ext i
  simp only [sideAllowed,Finset.mem_filter,Finset.mem_univ,true_and]
  cases hb : b <;> cases h0 : s (i-1) <;> cases h1 : s i <;> decide
lemma side_compatible_not (s : Fin 5 → Bool) (p : Finset (Fin 5)) :
    SideCompatible (fun i => !(s i)) p ↔ SideCompatible s p := by
  simp only [SideCompatible,side_allowed_not,Bool.not_true,Bool.not_false]
  tauto
lemma five_triple_forced : ∀a b c d : Fin 5,
    fiveAdj a b → fiveAdj b c → fiveAdj c d → (d=a ∨ d=a+2 ∨ d=a-2) →
    b=a+1 ∧ c=b+1 ∧ d=c+1 ∨ a=b+1 ∧ b=c+1 ∧ c=d+1 := by decide
lemma five_six_constant_steps_impossible : ∀a b c d e f : Fin 5,
    (b=a+1 ∧ c=b+1 ∧ d=c+1 ∨ a=b+1 ∧ b=c+1 ∧ c=d+1) →
    (e=d+1 ∧ f=e+1 ∧ a=f+1 ∨ d=e+1 ∧ e=f+1 ∧ f=a+1) →
    (c=b+1 ∧ d=c+1 ∧ e=d+1 ∨ b=c+1 ∧ c=d+1 ∧ d=e+1) → False := by decide
lemma five_word_impossible (p : Fin 6 → Fin 5)
    (ha : ∀j,fiveAdj (p j) (p (j+1)))
    (ho : ∀j,p (j+3)=p j ∨ p (j+3)=p j+2 ∨ p (j+3)=p j-2) : False := by
  have h0 := five_triple_forced (p 0) (p 1) (p 2) (p 3) (ha 0) (ha 1) (ha 2) (ho 0)
  have h3 := five_triple_forced (p 3) (p 4) (p 5) (p 0) (ha 3) (ha 4) (ha 5) (ho 3)
  have h1 := five_triple_forced (p 1) (p 2) (p 3) (p 4) (ha 1) (ha 2) (ha 3) (ho 1)
  exact five_six_constant_steps_impossible _ _ _ _ _ _ h0 h3 h1
lemma five_strip_orbit_impossible (s : Fin 6 → Fin 5 → Bool) (P : Fin 6 → Finset (Fin 5))
    (hp : ∀j,SideCompatible (s j) (P j))
    (hopp : ∀j i,s (j+3) i= !(s j i))
    (hdis : ∀j,Disjoint (P j) (P (j+1))) : False := by
  let p : Fin 6 → Fin 5 := fun j => fiveCanonical (P j)
  have he (j) : P j=fiveDiag (p j) := side_compatible_diagonal (s j) (P j) (hp j)
  apply five_word_impossible p
  · intro j
    exact (five_diag_disjoint _ _).mp (by rw [← he,← he]; exact hdis j)
  · intro j
    apply side_compatible_options (s j)
    · rw [← he]; exact hp j
    · have ho : s (j+3)=(fun i => !(s j i)) := funext (hopp j)
      have hh := hp (j+3)
      rw [ho,side_compatible_not,he] at hh
      exact hh
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
def angularSign (v : Fin 5 → ℂ) (t : Angles) (i : Fin 5) : Bool := decide (0<⟪direction t,v i⟫)
lemma angularSign_opposite {v : Fin 5 → ℂ} {t : Angles} (h : ∀i,⟪direction t,v i⟫≠0) :
    ∀i,angularSign v (t+(Real.pi : Angles)) i= !(angularSign v t i) := by
  intro i
  simp only [angularSign,direction_add_pi,inner_neg_left]
  by_cases hi : 0<⟪direction t,v i⟫
  · simp only [hi,show ¬0< -⟪direction t,v i⟫ by linarith,decide_true,decide_false,Bool.not_true]
  · have hn : ⟪direction t,v i⟫<0 := lt_of_le_of_ne (le_of_not_gt hi) (h i)
    simp only [hi,show 0< -⟪direction t,v i⟫ by linarith,decide_true,decide_false,Bool.not_false]
variable (c : ℂ → Fin 5) (hc : Measurable c)
lemma five_sides_compatible (hw : WeakColoring 5 c) {x : ℂ}
    {K : Fin 5 → Set ℂ} {v : Fin 5 → ℂ} (hv : ∀i,‖v i‖=1)
    (hK : ∀i,ApproachingContinuum x (K i) (v i))
    (hH : ∀i,Disjoint (spatialSupport c i) (Straddle (K i)) ∧
      Disjoint (spatialSupport c (i+1)) (Straddle (K i))) :
    ∀ᵐt∂angularMeasure,SideCompatible (angularSign v t) (palette c hc x t) := by
  let E (s : Fin 5 → Bool) (b : Bool) : Finset (Fin 5) := Finset.univ.filter fun i => s i=b
  have hex := finite_support_exclusion_ae c hc K (fun i => {i,i+1})
    (fun i j hj => by
      rcases Finset.mem_insert.mp hj with rfl|hj
      · exact (hH _).1
      · rw [Finset.mem_singleton] at hj; subst j; exact (hH _).2)
  have hJ (s : Fin 5 → Bool) (b : Bool) :
      ∀ᵐz : ℂ∂volume,(∀i∈E s b,z∈Straddle (K i)) → c z∈sideAllowed s b := by
    filter_upwards [hex] with z hz hzE
    simp only [sideAllowed,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · intro he
      have hmem : c z-1∈E s b := Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩
      apply hz (c z-1) (hzE _ hmem)
      simp
    · intro he
      have hmem : c z∈E s b := Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩
      exact hz (c z) (hzE _ hmem) (Finset.mem_insert_self _ _)
  have hout (s : Fin 5 → Bool) := continuum_outer_restriction c hc (E s true) hK (hJ s true)
  have hin (s : Fin 5 → Bool) := continuum_inner_restriction c hc (E s false) hK (hJ s false)
  filter_upwards [ae_all_iff.mpr hout,ae_all_iff.mpr hin,palette_cardinality c hc hw x,
    ae_all_iff.mpr (fun i => ae_direction_nonorthogonal (hv i))] with t ho hi hp hn
  refine ⟨hp.2,ho (angularSign v t) ?_,hi (angularSign v t) ?_⟩
  · intro i hi
    have hh : angularSign v t i=true := (Finset.mem_filter.mp hi).2
    exact of_decide_eq_true hh
  · intro i hi
    have hh : angularSign v t i=false := (Finset.mem_filter.mp hi).2
    have hn' : ¬0<⟪direction t,v i⟫ := of_decide_eq_false hh
    exact lt_of_le_of_ne (le_of_not_gt hn') (hn i)
include hc in
/-- Actual five-cycle angular obstruction under exactly the directional and
common-support-exclusion data extracted in source Proposition interface-cycle.
This does not assert that such data have been extracted. -/
lemma no_five_exclusion_continua (hw : WeakColoring 5 c) {x : ℂ}
    {K : Fin 5 → Set ℂ} {v : Fin 5 → ℂ} (hv : ∀i,‖v i‖=1)
    (hK : ∀i,ApproachingContinuum x (K i) (v i))
    (hH : ∀i,Disjoint (spatialSupport c i) (Straddle (K i)) ∧
      Disjoint (spatialSupport c (i+1)) (Straddle (K i))) : False := by
  have hh := (five_sides_compatible c hc hw hv hK hH).and
    ((palette_sixty_disjoint c hc hw x).and (ae_all_iff.mpr (fun i => ae_direction_nonorthogonal (hv i))))
  have hshift (j : Fin 6) := (measurePreserving_add_right angularMeasure (sixAngle j)).quasiMeasurePreserving.ae hh
  obtain ⟨t,ht⟩ := (ae_all_iff.mpr hshift).exists
  apply five_strip_orbit_impossible
    (fun j => angularSign v (t+sixAngle j)) (fun j => palette c hc x (t+sixAngle j))
  · intro j; exact (ht j).1
  · intro j i
    rw [sixAngle_half,← add_assoc]
    exact angularSign_opposite (ht j).2.2 i
  · intro j
    rw [sixAngle_step,← add_assoc]
    exact (ht j).2.1
end EuclideanFiveColor
end

end OAI
