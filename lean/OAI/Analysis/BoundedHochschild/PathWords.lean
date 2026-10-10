import Mathlib
import OAI.Analysis.BoundedHochschild.FinitePaths
import OAI.Analysis.BoundedHochschild.FreeCoefficients

namespace OAI

/-! Formal path words, free-group retractions and simultaneous path moments. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
namespace HochschildPaths
variable {C D : Type*} {r n : ℕ}

def signed {G : Type*} [Group G] (g : G) (b : Bool) : G := if b then g else g⁻¹

@[simp] lemma signed_signed {G : Type*} [Group G] (g : G) (b : Bool) :
    signed (signed g b) b=g := by cases b <;> simp [signed]

@[simp] lemma signed_one {G : Type*} [Group G] (b : Bool) : signed (1:G) b=1 := by
  cases b <;> simp [signed]

lemma map_signed {G H : Type*} [Group G] [Group H] (f : G →* H) (g : G) (b : Bool) :
    f (signed g b)=signed (f g) b := by cases b <;> simp [signed]

lemma prod_ofFn_single {G : Type*} [Monoid G] {n : ℕ} (f : Fin n → G) (j : Fin n)
    (hf : ∀ i, i ≠ j → f i=1) : (List.ofFn f).prod=f j := by
  induction n with
  | zero => exact j.elim0
  | succ n ih =>
    rw [List.ofFn_succ,List.prod_cons]
    induction j using Fin.cases with
    | zero =>
      have h : (List.ofFn fun i : Fin n => f i.succ).prod=1 := by
        apply List.prod_eq_one
        intro a ha
        obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
        exact hf i.succ (Fin.succ_ne_zero i)
      rw [h,mul_one]
    | succ j =>
      rw [hf 0 (Ne.symm (Fin.succ_ne_zero j)),one_mul]
      apply ih
      intro i hi
      exact hf i.succ (fun h => hi (Fin.succ_injective _ h))

variable (w : Fin r × Fin n → (C ⊕ D) × Bool)
  (s : Fin r → Fin n) (a : Fin r → D)
  (hpos : ∀ i, (w (i,s i)).1=Sum.inr (a i))
  (huniq : ∀ i z, (w z).1=Sum.inr (a i) → z=(i,s i))

include hpos huniq in
lemma distinguished_injective : Function.Injective a := by
  intro i j hij
  have h := huniq i (j,s j) ((hpos j).trans (congrArg Sum.inr hij.symm))
  exact (congrArg Prod.fst h).symm

 

def retractLetter (x : C ⊕ D) : FreeGroup (Fin r) := by
  classical
  exact if h : ∃ i, x=Sum.inr (a i) then
    signed (FreeGroup.of h.choose) (w (h.choose,s h.choose)).2
  else 1

include hpos huniq in
lemma retractLetter_distinguished (i : Fin r) :
    retractLetter w s a (Sum.inr (a i))=signed (FreeGroup.of i) (w (i,s i)).2 := by
  classical
  unfold retractLetter
  split_ifs with h
  · have hi : h.choose=i := distinguished_injective w s a hpos huniq
      (Sum.inr.inj h.choose_spec).symm
    simp only [hi]
  · exact False.elim (h ⟨i,rfl⟩)

include huniq in
lemma retractLetter_away (i : Fin r) (j : Fin n) (hj : j ≠ s i) :
    retractLetter w s a (w (i,j)).1=1 := by
  classical
  unfold retractLetter
  split_ifs with h
  · have hz := huniq h.choose (i,j) h.choose_spec
    have hi : i=h.choose := congrArg Prod.fst hz
    have hs : j=s i := (congrArg Prod.snd hz).trans (congrArg s hi.symm)
    exact False.elim (hj hs)
  · rfl

def formalPath (i : Fin r) : FreeGroup (C ⊕ D) :=
  (List.ofFn fun j => signed (FreeGroup.of (w (i,j)).1) (w (i,j)).2).prod

def pathHom : FreeGroup (Fin r) →* FreeGroup (C ⊕ D) :=
  FreeGroup.lift (formalPath w)

def retractHom : FreeGroup (C ⊕ D) →* FreeGroup (Fin r) :=
  FreeGroup.lift (retractLetter w s a)

include hpos huniq in
lemma retract_formalPath (i : Fin r) :
    retractHom w s a (formalPath w i)=FreeGroup.of i := by
  classical
  simp only [formalPath,map_list_prod,List.map_ofFn,retractHom]
  rw [prod_ofFn_single _ (s i)]
  · simp only [Function.comp_apply,map_signed,FreeGroup.lift_apply_of]
    rw [hpos,retractLetter_distinguished w s a hpos huniq,signed_signed]
  · intro j hj
    simp only [Function.comp_apply,map_signed,FreeGroup.lift_apply_of]
    rw [retractLetter_away w s a huniq i j hj,signed_one]

include hpos huniq in
 

theorem retract_pathHom (q : FreeGroup (Fin r)) :
    retractHom w s a (pathHom w q)=q := by
  have h : (retractHom w s a).comp (pathHom w)=MonoidHom.id _ := by
    apply FreeGroup.ext_hom
    intro i
    simp only [MonoidHom.comp_apply,pathHom,FreeGroup.lift_apply_of,MonoidHom.id_apply]
    exact retract_formalPath w s a hpos huniq i
  exact congrArg (fun f : FreeGroup (Fin r) →* FreeGroup (Fin r) => f q) h

include hpos huniq in
theorem pathHom_injective : Function.Injective (pathHom w) := by
  intro q t h
  have hh := congrArg (retractHom w s a) h
  simpa only [retract_pathHom w s a hpos huniq] using hh

include hpos huniq in
theorem pathHom_ne_one (q : FreeGroup (Fin r)) (hq : q ≠ 1) : pathHom w q ≠ 1 := by
  intro h
  apply hq
  apply pathHom_injective w s a hpos huniq
  simpa using h

 
def freshProjection : FreeGroup (C ⊕ D) →* FreeGroup D :=
  FreeGroup.lift (Sum.elim (fun _ : C => 1) FreeGroup.of)

lemma retract_factors :
    (FreeGroup.lift (fun d : D => retractLetter w s a (Sum.inr d))).comp
      (freshProjection (C := C) (D := D)) = retractHom w s a := by
  classical
  apply FreeGroup.ext_hom
  intro z
  cases z with
  | inl c =>
    simp [freshProjection,retractHom,retractLetter]
  | inr d =>
    simp only [MonoidHom.comp_apply,freshProjection,FreeGroup.lift_apply_of,
      Sum.elim_inr,retractHom]

include hpos huniq in
 

theorem freshProjection_pathHom_ne_one (q : FreeGroup (Fin r)) (hq : q ≠ 1) :
    freshProjection (pathHom w q) ≠ 1 := by
  intro h
  have hh := congrArg (FreeGroup.lift (fun d : D => retractLetter w s a (Sum.inr d))) h
  change ((FreeGroup.lift (fun d : D => retractLetter w s a (Sum.inr d))).comp
    freshProjection) (pathHom w q)=_ at hh
  rw [retract_factors,retract_pathHom w s a hpos huniq,map_one] at hh
  exact hq hh

end HochschildPaths
 

 

namespace HochschildPaths
variable {M C D : Type*} [Ring M] [Algebra ℂ M]
  (B : Subalgebra ℂ M) (v : C → Bˣ) (u : D → Mˣ)

def unitaryEvaluation : FreeGroup (C ⊕ D) →* Mˣ :=
  FreeGroup.lift (Sum.elim (fun c => Units.map B.val.toMonoidHom (v c)) u)

def freshEvaluation : FreeGroup D →* M :=
  (Units.coeHom M).comp (FreeGroup.lift u)

def encodeLetter : (C ⊕ D) × Bool → HochschildFreeMoments.Letter B (G := FreeGroup D)
  | (.inl c,b) => .inl (signed (v c) b : Bˣ)
  | (.inr d,b) => .inr (signed (FreeGroup.of d) b)

lemma value_encode (x : (C ⊕ D) × Bool) :
    HochschildFreeMoments.value B (freshEvaluation u) (encodeLetter B v x)=
      ((signed ((Sum.elim (fun c => Units.map B.val.toMonoidHom (v c)) u) x.1) x.2 : Mˣ) : M) := by
  rcases x with ⟨c|d,b⟩ <;> cases b <;>
    simp [encodeLetter,HochschildFreeMoments.value,freshEvaluation,signed]

lemma degree_encode (x : (C ⊕ D) × Bool) :
    HochschildFreeMoments.degreeLetter B (encodeLetter B v x)=
      signed ((Sum.elim (fun _ : C => 1) FreeGroup.of) x.1) x.2 := by
  rcases x with ⟨c|d,b⟩ <;> cases b <;>
    simp [encodeLetter,HochschildFreeMoments.degreeLetter,signed]

lemma evaluate_encode (l : List ((C ⊕ D) × Bool)) :
    HochschildFreeMoments.evaluate B (freshEvaluation u) (l.map (encodeLetter B v))=
      ((unitaryEvaluation B v u (FreeGroup.mk l) : Mˣ) : M) := by
  simp only [HochschildFreeMoments.evaluate,List.map_map,unitaryEvaluation,FreeGroup.lift_mk]
  change _ = (Units.coeHom M) ((l.map _).prod)
  rw [map_list_prod,List.map_map]
  congr 2
  funext x
  rw [Function.comp_apply,value_encode]
  rcases x with ⟨z,b⟩
  cases b <;> rfl

lemma degree_encode_list (l : List ((C ⊕ D) × Bool)) :
    HochschildFreeMoments.degree B (l.map (encodeLetter B v))=
      freshProjection (FreeGroup.mk l) := by
  simp only [HochschildFreeMoments.degree,List.map_map,freshProjection,FreeGroup.lift_mk]
  congr 2
  funext x
  rw [Function.comp_apply,degree_encode]
  rcases x with ⟨z,b⟩
  cases b <;> rfl

 

theorem moment_eq_zero_of_fresh_ne_one (τ : M →ₗ[ℂ] ℂ)
    (h1 : τ 1=1) (hu : ∀ g : FreeGroup D, g ≠ 1 → τ (freshEvaluation u g)=0)
    (hfree : HochschildFreeMoments.FreeCoefficients B (freshEvaluation u) τ)
    (g : FreeGroup (C ⊕ D)) (hg : freshProjection g ≠ 1) :
    τ (unitaryEvaluation B v u g : M)=0 := by
  induction g using Quot.inductionOn with
  | h l =>
    have h := HochschildFreeMoments.moment_eq_zero_of_degree_ne_one B
      (freshEvaluation u) τ h1 hu hfree (l.map (encodeLetter B v))
      (by rwa [degree_encode_list])
    rwa [evaluate_encode] at h

 

theorem distinguished_paths_moment (τ : M →ₗ[ℂ] ℂ)
    (h1 : τ 1=1) (hu : ∀ g : FreeGroup D, g ≠ 1 → τ (freshEvaluation u g)=0)
    (hfree : HochschildFreeMoments.FreeCoefficients B (freshEvaluation u) τ)
    {r n : ℕ} (w : Fin r × Fin n → (C ⊕ D) × Bool)
    (s : Fin r → Fin n) (a : Fin r → D)
    (hpos : ∀ i, (w (i,s i)).1=Sum.inr (a i))
    (huniq : ∀ i z, (w z).1=Sum.inr (a i) → z=(i,s i))
    (q : FreeGroup (Fin r)) (hq : q ≠ 1) :
    τ (unitaryEvaluation B v u (pathHom w q) : M)=0 :=
  moment_eq_zero_of_fresh_ne_one B v u τ h1 hu hfree _
    (freshProjection_pathHom_ne_one w s a hpos huniq q hq)

end HochschildPaths

 

open Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
namespace HochschildPaths
open HochschildUltrapower HochschildRare
variable {M C D : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  (τ : M →ₚ[ℂ] ℂ) (h1 : τ 1=1) (ω : Ultrafilter ℕ)
  (htr : ∀ a b : M, τ (a*b)=τ (b*a))

omit [PartialOrder M] [StarOrderedRing M] in
lemma lift_pathValue_formal {r n : ℕ} (v : C ⊕ D → unitary M)
    (w : Fin r × Fin n → (C ⊕ D) × Bool) (q : FreeGroup (Fin r)) :
    FreeGroup.lift (pathValue v w) q = FreeGroup.lift v (pathHom w q) := by
  have h : FreeGroup.lift (pathValue v w)=(FreeGroup.lift v).comp (pathHom w) := by
    apply FreeGroup.ext_hom
    intro i
    simp only [FreeGroup.lift_apply_of,MonoidHom.comp_apply,pathHom,formalPath,
      map_list_prod,List.map_ofFn,pathValue,HochschildWalk.word]
    congr 2
    funext j
    change signedValue v (w (i,j))=FreeGroup.lift v (signed (FreeGroup.of (w (i,j)).1) (w (i,j)).2)
    rw [map_signed,FreeGroup.lift_apply_of]
    rfl
  exact congrArg (fun f : FreeGroup (Fin r) →* unitary M => f q) h

 

def mixedFamily (v : C → unitary M) (u : ℕ → D → unitary M) :
    FreeGroup (C ⊕ D) →* Ultrapower τ h1 ω htr :=
  quotientFamily τ h1 ω htr (fun j => FreeGroup.lift (Sum.elim v (u j)))

def freshUnits (u : ℕ → D → unitary M) (d : D) : (Ultrapower τ h1 ω htr)ˣ :=
  (quotientFamily τ h1 ω htr (fun j => FreeGroup.lift (u j))).toHomUnits (FreeGroup.of d)

lemma mixedFamily_of_inl (v : C → unitary M) (u : ℕ → D → unitary M) (c : C) :
    mixedFamily τ h1 ω htr v u (FreeGroup.of (Sum.inl c)) =
      constant τ h1 ω htr (v c : M) := by
  apply congrArg (quotientHom τ h1 ω htr)
  ext j
  simp only [boundedHom_apply,FreeGroup.lift_apply_of,Sum.elim_inl]
  rfl

lemma mixedFamily_of_inr (v : C → unitary M) (u : ℕ → D → unitary M) (d : D) :
    mixedFamily τ h1 ω htr v u (FreeGroup.of (Sum.inr d)) =
      (freshUnits τ h1 ω htr u d : Ultrapower τ h1 ω htr) := by
  apply congrArg (quotientHom τ h1 ω htr)
  ext j
  simp only [boundedHom_apply,FreeGroup.lift_apply_of,Sum.elim_inr]

lemma mixedFamily_eq_eval (v : C → unitary M) (u : ℕ → D → unitary M)
    (B : Subalgebra ℂ (Ultrapower τ h1 ω htr)) (b : C → Bˣ)
    (hb : ∀ c, ((b c : B) : Ultrapower τ h1 ω htr)=constant τ h1 ω htr (v c : M))
    (g : FreeGroup (C ⊕ D)) :
    mixedFamily τ h1 ω htr v u g=
      (unitaryEvaluation B b (freshUnits τ h1 ω htr u) g : Ultrapower τ h1 ω htr) := by
  have h : mixedFamily τ h1 ω htr v u =
      (Units.coeHom _).comp (unitaryEvaluation B b (freshUnits τ h1 ω htr u)) := by
    apply FreeGroup.ext_hom
    intro z
    cases z with
    | inl c =>
      simp only [MonoidHom.comp_apply,unitaryEvaluation,FreeGroup.lift_apply_of,Sum.elim_inl]
      exact (mixedFamily_of_inl τ h1 ω htr v u c).trans (hb c).symm
    | inr d =>
      simp only [MonoidHom.comp_apply,unitaryEvaluation,FreeGroup.lift_apply_of,Sum.elim_inr]
      exact mixedFamily_of_inr τ h1 ω htr v u d
  exact congrArg (fun f : FreeGroup (C ⊕ D) →* Ultrapower τ h1 ω htr => f g) h

 

theorem simultaneous_paths_of_free_lifts
    (v : C → unitary M) (u : ℕ → D → unitary M)
    (B : Subalgebra ℂ (Ultrapower τ h1 ω htr)) (b : C → Bˣ)
    (hb : ∀ c, ((b c : B) : Ultrapower τ h1 ω htr)=constant τ h1 ω htr (v c : M))
    (hu : ∀ g : FreeGroup D, g ≠ 1 →
      quotientTrace τ h1 ω htr (freshEvaluation (freshUnits τ h1 ω htr u) g)=0)
    (hfree : HochschildFreeMoments.FreeCoefficients B
      (freshEvaluation (freshUnits τ h1 ω htr u)) (quotientTrace τ h1 ω htr).toLinearMap)
    {T : Type*} [Finite T] (r n : T → ℕ)
    (w : ∀ t, Fin (r t) × Fin (n t) → (C ⊕ D) × Bool)
    (q : ∀ t, FreeGroup (Fin (r t))) (hq : ∀ t, q t ≠ 1)
    (hletters : ∀ t, ∃ (s : Fin (r t) → Fin (n t)) (a : Fin (r t) → D),
      (∀ i, (w t (i,s i)).1=Sum.inr (a i)) ∧
      (∀ i z, (w t z).1=Sum.inr (a i) → z=(i,s i)))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ j : ℕ, ∀ t,
      ‖τ (FreeGroup.lift (pathValue (Sum.elim v (u j)) (w t)) (q t) : M)‖ < ε := by
  have ht (t : T) : Tendsto
      (fun j => τ (FreeGroup.lift (pathValue (Sum.elim v (u j)) (w t)) (q t) : M))
      (ω : Filter ℕ) (nhds 0) := by
    obtain ⟨s,a,hpos,huniq⟩ := hletters t
    have hz := distinguished_paths_moment B b (freshUnits τ h1 ω htr u)
      (quotientTrace τ h1 ω htr).toLinearMap (quotientTrace_one τ h1 ω htr)
      hu hfree (w t) s a hpos huniq (q t) (hq t)
    rw [← mixedFamily_eq_eval τ h1 ω htr v u B b hb] at hz
    have hc := tendsto_sequenceTrace τ h1 ω
      (boundedHom (fun j => FreeGroup.lift (Sum.elim v (u j))) (pathHom (w t) (q t)))
    change Tendsto (fun j => τ (FreeGroup.lift (Sum.elim v (u j)) (pathHom (w t) (q t)) : M))
      (ω : Filter ℕ) (nhds (quotientTrace τ h1 ω htr
        (mixedFamily τ h1 ω htr v u (pathHom (w t) (q t))))) at hc
    change quotientTrace τ h1 ω htr
      (mixedFamily τ h1 ω htr v u (pathHom (w t) (q t)))=0 at hz
    rw [hz] at hc
    simpa only [lift_pathValue_formal] using hc
  have he : ∀ᶠ j in (ω : Filter ℕ), ∀ t,
      ‖τ (FreeGroup.lift (pathValue (Sum.elim v (u j)) (w t)) (q t) : M)‖ < ε := by
    apply eventually_all.mpr
    intro t
    have he := (ht t).eventually (Metric.ball_mem_nhds (0:ℂ) hε)
    simpa only [Metric.mem_ball,dist_zero_right] using he
  exact he.exists

end HochschildPaths
end

end OAI
