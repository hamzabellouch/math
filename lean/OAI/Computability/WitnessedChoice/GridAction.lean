import OAI.Computability.WitnessedChoice.SupportGrid

namespace OAI

namespace WitnessedSeparation.Grid

noncomputable section

open Support

def pairing {ι : Type*} [Fintype ι] (l : ι → Scalar) : (ι → Scalar) →ₗ[Scalar] Scalar where
  toFun z := ∑ e, l e * z e
  map_add' := by intros; simp [mul_add, Finset.sum_add_distrib]
  map_smul' := by intros; simp [Finset.mul_sum, mul_left_comm]

@[simp] theorem pairing_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    (l : ι → Scalar) (e : ι) (z : Scalar) : pairing l (Pi.single e z) = l e * z := by
  classical
  change (∑ j, l j * (Pi.single e z : ι → Scalar) j) = _
  simp only [Pi.single_apply, mul_ite, mul_zero]
  simp

variable {n : ℕ}

theorem pairing_boundary (φ : Vertex n → Scalar) (z : Edge n → Scalar) :
    pairing φ (boundary z) = pairing (gradient φ) z := by
  have hb : boundary z = ∑ e : Edge n, z e •
      ((Pi.single (head e) (1 : Scalar) : Vertex n → Scalar) - Pi.single (tail e) 1) := rfl
  rw [hb]
  simp only [map_sum, map_smul, map_sub, pairing_single, mul_one, smul_eq_mul]
  change (∑ e, z e * (φ (head e) - φ (tail e))) =
    ∑ e, (φ (head e) - φ (tail e)) * z e
  apply Finset.sum_congr rfl
  intro e _
  ring

abbrev FlowSpace (n : ℕ) := (boundary (n := n)).ker

def flowCycle (f : Face n) : FlowSpace n := ⟨cycle f, boundary_cycle f⟩

@[simp] theorem pairing_gradient_flow (φ : Vertex n → Scalar) (k : FlowSpace n) :
    pairing (gradient φ) k.val = 0 := by
  rw [← pairing_boundary, LinearMap.mem_ker.mp k.property, map_zero]

theorem pairing_sub {ι : Type*} [Fintype ι] (l r z : ι → Scalar) :
    pairing (l-r) z = pairing l z - pairing r z := by
  simp only [pairing, LinearMap.coe_mk, AddHom.coe_mk, Pi.sub_apply,
    sub_mul, Finset.sum_sub_distrib]

theorem exists_representative (lambda : FlowSpace n →ₗ[Scalar] Scalar) :
    ∃ l : Edge n → Scalar, ∀ k : FlowSpace n, pairing l k.val = lambda k := by
  obtain ⟨g,hg⟩ := LinearMap.exists_extend lambda
  let l : Edge n → Scalar := fun e => g (Pi.single e 1)
  have hrep (z : Edge n → Scalar) : g z = pairing l z := by
    have hz : (∑ e : Edge n, z e • Pi.single e (1 : Scalar)) = z := by
      classical
      ext e
      simp [Finset.sum_apply, Pi.single_apply]
    calc
      g z = g (∑ e : Edge n, z e • Pi.single e (1 : Scalar)) := congrArg g hz.symm
      _ = ∑ e, z e * l e := by simp only [map_sum, map_smul, smul_eq_mul]; rfl
      _ = pairing l z := by
        change (∑ e, z e * l e) = ∑ e, l e * z e
        apply Finset.sum_congr rfl
        intro e _
        ring
  refine ⟨l, fun k => ?_⟩
  rw [← hrep]
  exact LinearMap.congr_fun hg k

theorem curl_representative (lambda : FlowSpace n →ₗ[Scalar] Scalar) (l : Edge n → Scalar)
    (hl : ∀ k : FlowSpace n, pairing l k.val = lambda k) (f : Face n) :
    curl l f = lambda (flowCycle f) := by
  rw [← hl]
  simp only [curl, pairing, LinearMap.coe_mk, AddHom.coe_mk, flowCycle, mul_comm]

abbrev BoxGroup (n : ℕ) := Support.H (flowCycle (n := n))

def faceCodim (S : Subgroup (BoxGroup n)) : ℕ :=
  Module.finrank Scalar (Face n → Support.Plane) -
    Module.finrank Scalar (Support.H.projected flowCycle S)

def flowCodim (S : Subgroup (BoxGroup n)) : ℕ :=
  Module.finrank Scalar (FlowSpace n) -
    Module.finrank Scalar (Support.H.centralPart flowCycle S)

theorem curl_count_le_codim (S : Subgroup (BoxGroup n))
    (lambda : FlowSpace n →ₗ[Scalar] Scalar)
    (hlambda : lambda ∈ (Support.H.centralPart flowCycle S).dualAnnihilator)
    (l : Edge n → Scalar) (hl : ∀ k : FlowSpace n, pairing l k.val = lambda k) :
    (nonzeroSet (curl l)).card ≤ faceCodim S := by
  classical
  have hiso : ∀ a ∈ Support.H.projected flowCycle S,
      ∀ b ∈ Support.H.projected flowCycle S, Support.diagonalForm (curl l) a b = 0 := by
    intro a ha b hb
    simp only [Support.diagonalForm_apply, curl_representative lambda l hl]
    exact Support.H.stabilizer_isotropic flowCycle S lambda
      ((Submodule.mem_dualAnnihilator lambda).mp hlambda) ha hb
  have h := Support.nonzero_blocks_le_codim (curl l)
    (Support.H.projected flowCycle S) hiso
  simpa only [nonzeroSet, faceCodim, Fintype.card_subtype] using h

theorem sparse_annihilator (S : Subgroup (BoxGroup n))
    (lambda : FlowSpace n →ₗ[Scalar] Scalar)
    (hlambda : lambda ∈ (Support.H.centralPart flowCycle S).dualAnnihilator) :
    ∃ r : Edge n → Scalar,
      (∀ k : FlowSpace n, pairing r k.val = lambda k) ∧
      (nonzeroSet r).card ≤ (n+1) * faceCodim S := by
  obtain ⟨l,hl⟩ := exists_representative lambda
  obtain ⟨φ,hφ⟩ := sparse_cochain l
  refine ⟨l - gradient φ, ?_, hφ.trans (Nat.mul_le_mul_left _ (curl_count_le_codim S lambda hlambda l hl))⟩
  intro k
  rw [pairing_sub, pairing_gradient_flow, sub_zero, hl]

theorem subgroup_support_edges (S : Subgroup (BoxGroup n)) :
    ∃ T : Finset (Edge n),
      T.card ≤ (n+1) * faceCodim S * flowCodim S ∧
      ∀ k : FlowSpace n, (∀ e ∈ T, k.val e = 0) →
        Support.H.central flowCycle k ∈ S := by
  classical
  let W := (Support.H.centralPart flowCycle S).dualAnnihilator
  let : Module.Free Scalar W := Module.Free.of_divisionRing Scalar W
  let b := Module.finBasis Scalar W
  have hd : Module.finrank Scalar W = flowCodim S := by
    have h := Subspace.finrank_add_finrank_dualAnnihilator_eq
      (Support.H.centralPart flowCycle S)
    change Module.finrank Scalar (Support.H.centralPart flowCycle S) +
      Module.finrank Scalar W = Module.finrank Scalar (FlowSpace n) at h
    unfold flowCodim
    omega
  have hr : ∀ i : Fin (Module.finrank Scalar W), ∃ r : Edge n → Scalar,
      (∀ k : FlowSpace n, pairing r k.val = (b i).val k) ∧
      (nonzeroSet r).card ≤ (n+1) * faceCodim S := by
    intro i
    exact sparse_annihilator S (b i).val (b i).property
  choose r hr hbnd using hr
  let T := Finset.univ.biUnion (fun i => nonzeroSet (r i))
  refine ⟨T, ?_, ?_⟩
  · calc
      T.card ≤ ∑ i : Fin (Module.finrank Scalar W), (nonzeroSet (r i)).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _ : Fin (Module.finrank Scalar W), (n+1) * faceCodim S :=
        Finset.sum_le_sum (fun i _ => hbnd i)
      _ = (n+1) * faceCodim S * flowCodim S := by simp [hd, Nat.mul_comm]
  · intro k hk
    apply (Support.H.mem_centralPart flowCycle S k).mp
    apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff
      (Support.H.centralPart flowCycle S) k).mp
    have hbi (i : Fin (Module.finrank Scalar W)) : (b i).val k = 0 := by
      rw [← hr i k]
      change (∑ e, r i e * k.val e) = 0
      apply Finset.sum_eq_zero
      intro e _
      by_cases he : r i e = 0
      · simp [he]
      · have hmem : e ∈ T := Finset.mem_biUnion.mpr
          ⟨i, Finset.mem_univ _, (mem_nonzeroSet _ _).mpr he⟩
        simp [hk e hmem]
    intro lambda hlambda
    let w : W := ⟨lambda, hlambda⟩
    have heq := congrArg (fun w : W => w.val k) (b.sum_repr w)
    simp only [Submodule.coe_sum, Submodule.coe_smul, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul, hbi, mul_zero, Finset.sum_const_zero] at heq
    exact heq.symm

theorem box_subgroup_index (S : Subgroup (BoxGroup n)) :
    S.index = 3 ^ (faceCodim S + flowCodim S) :=
  Support.H.subgroup_index flowCycle S

theorem orbit_card_eq_power {X : Type*} [MulAction (BoxGroup n) X] (x : X) :
    Nat.card (MulAction.orbit (BoxGroup n) x) =
      3 ^ (faceCodim (MulAction.stabilizer (BoxGroup n) x) +
        flowCodim (MulAction.stabilizer (BoxGroup n) x)) := by
  rw [Nat.card_congr (MulAction.orbitEquivQuotientStabilizer (BoxGroup n) x)]
  exact box_subgroup_index (MulAction.stabilizer (BoxGroup n) x)

theorem small_orbit_support_edges {X : Type*} [MulAction (BoxGroup n) X]
    (x : X) (N : ℕ) (hN : 0 < N) (q : ℝ) (_hq : 0 ≤ q)
    (horbit : (Nat.card (MulAction.orbit (BoxGroup n) x) : ℝ) ≤ (N : ℝ) ^ q) :
    ∃ T : Finset (Edge n),
      (T.card : ℝ) ≤ 2 * (n+1 : ℝ) * (q * Real.logb 3 N)^2 ∧
      ∀ k : FlowSpace n, (∀ e ∈ T, k.val e = 0) →
        Support.H.central flowCycle k • x = x := by
  let S := MulAction.stabilizer (BoxGroup n) x
  obtain ⟨T,hcard,hfix⟩ := subgroup_support_edges S
  have heq := orbit_card_eq_power (n := n) x
  have horbit' : (3 : ℝ) ^ (faceCodim S + flowCodim S) ≤ (N : ℝ) ^ q := by
    rw [heq, Nat.cast_pow, Nat.cast_ofNat] at horbit
    exact horbit
  have hlog := Real.logb_le_logb_of_le (b := 3) (by norm_num : (1 : ℝ) < 3)
    (by positivity : (0 : ℝ) < 3 ^ (faceCodim S + flowCodim S)) horbit'
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one,
    Real.logb_rpow_eq_mul_logb_of_pos (by exact_mod_cast hN), Nat.cast_add] at hlog
  have ha : 0 ≤ (faceCodim S : ℝ) := Nat.cast_nonneg _
  have hd : 0 ≤ (flowCodim S : ℝ) := Nat.cast_nonneg _
  have hab : (faceCodim S : ℝ) * flowCodim S ≤ (q * Real.logb 3 N)^2 := by
    nlinarith [sq_nonneg ((faceCodim S : ℝ) - flowCodim S)]
  have hc : (T.card : ℝ) ≤ (n+1 : ℝ) * faceCodim S * flowCodim S := by
    exact_mod_cast hcard
  refine ⟨T, ?_, fun k hk => hfix k hk⟩
  calc
    (T.card : ℝ) ≤ (n+1 : ℝ) * faceCodim S * flowCodim S := hc
    _ ≤ (n+1 : ℝ) * (q * Real.logb 3 N)^2 := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hab (by positivity)
    _ ≤ 2 * (n+1 : ℝ) * (q * Real.logb 3 N)^2 := by
      have hpos : 0 ≤ (n+1 : ℝ) * (q * Real.logb 3 N)^2 := by positivity
      nlinarith

end



open Support

variable {n : ℕ}

theorem sum_subtype_zero {ι M : Type*} [Fintype ι] [AddCommMonoid M]
    (p : ι → Prop) [DecidablePred p] (f : ι → M) (h : ∀ i, ¬ p i → f i = 0) :
    (∑ i : {x // p x}, f i.val) = ∑ i, f i := by
  have hz : (∑ i : {x // ¬ p x}, f i.val) = 0 :=
    Finset.sum_eq_zero (fun i _ => h i.val i.property)
  simpa only [hz,add_zero] using Fintype.sum_subtype_add_sum_subtype p f

abbrev EdgeFaces (e : Edge n) := {f : Face n // cycle f e ≠ 0}

def localCycle (e : Edge n) (f : EdgeFaces e) : Scalar := cycle f.val e

abbrev LocalGroup (e : Edge n) := Support.H (localCycle e)

noncomputable def restrictGroup (e : Edge n) : BoxGroup n →* LocalGroup e where
  toFun g := ⟨fun f => g.face f.val, g.flow.val e⟩
  map_one' := rfl
  map_mul' := by
    intro g h
    apply Support.H.ext
    · rfl
    · simp only [Support.H.mul_flow, Submodule.coe_add, Pi.add_apply]
      congr 1
      simp only [Support.correction, Submodule.coe_smul, Submodule.coe_sum,
        Pi.smul_apply, Finset.sum_apply, smul_eq_mul, flowCycle, localCycle]
      congr 1
      exact (sum_subtype_zero _ _ (fun f hf => by simp_all)).symm

@[simp] theorem restrictGroup_face (g : BoxGroup n) (e : Edge n) (f : EdgeFaces e) :
    (restrictGroup e g).face f = g.face f.val := rfl

@[simp] theorem restrictGroup_flow (g : BoxGroup n) (e : Edge n) :
    (restrictGroup e g).flow = g.flow.val e := rfl

def incident (v : Vertex n) (e : Edge n) : Prop := head e = v ∨ tail e = v

instance : DecidableRel (incident (n := n)) := fun v e =>
  inferInstanceAs (Decidable (head e = v ∨ tail e = v))

abbrev IncidentEdges (v : Vertex n) := {e : Edge n // incident v e}

noncomputable def epsilon (v : Vertex n) (e : Edge n) : Scalar :=
  (if head e = v then 1 else 0) - (if tail e = v then 1 else 0)

theorem boundary_eval (z : Edge n → Scalar) (v : Vertex n) :
    boundary z v = ∑ e, epsilon v e * z e := by
  classical
  simp only [boundary, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply,
    Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro e _
  simp [epsilon, Pi.single_apply, eq_comm, mul_comm]

theorem epsilon_eq_zero (v : Vertex n) (e : Edge n) (h : ¬ incident v e) :
    epsilon v e = 0 := by
  classical
  simp only [incident, not_or] at h
  simp [epsilon,h.1,h.2]

theorem sum_incident (z : Edge n → Scalar) (v : Vertex n) :
    (∑ e : IncidentEdges v, epsilon v e.val * z e.val) = boundary z v := by
  classical
  rw [boundary_eval]
  exact sum_subtype_zero (incident v) (fun e => epsilon v e * z e)
    (fun e he => by rw [epsilon_eq_zero v e he,zero_mul])

abbrev LocalStates (v : Vertex n) := (e : IncidentEdges v) → LocalGroup e.val

def Compatible {v : Vertex n} (s : LocalStates v) : Prop :=
  ∀ (e e' : IncidentEdges v) (f : Face n) (h : cycle f e.val ≠ 0)
    (h' : cycle f e'.val ≠ 0),
    (s e).face ⟨f,h⟩ = (s e').face ⟨f,h'⟩

theorem compatible_iff_extend {v : Vertex n} (s : LocalStates v) :
    Compatible s ↔ ∃ u : Face n → Plane,
      ∀ (e : IncidentEdges v) (f : EdgeFaces e.val), (s e).face f = u f.val := by
  classical
  constructor
  · intro h
    let u (f : Face n) : Plane := if hh : ∃ e : IncidentEdges v, cycle f e.val ≠ 0
      then (s hh.choose).face ⟨f,hh.choose_spec⟩ else 0
    refine ⟨u,?_⟩
    intro e f
    have hh : ∃ e : IncidentEdges v, cycle f.val e.val ≠ 0 := ⟨e,f.property⟩
    simp only [u,dite_eq_left hh]
    exact h e hh.choose f.val f.property hh.choose_spec
  · rintro ⟨u,h⟩ e e' f hf hf'
    rw [h e ⟨f,hf⟩, h e' ⟨f,hf'⟩]

noncomputable def divergence {v : Vertex n} (s : LocalStates v) : Scalar :=
  ∑ e : IncidentEdges v, epsilon v e.val * (s e).flow

structure Configuration (b : Vertex n → Scalar) (v : Vertex n) where
  state : LocalStates v
  compatible : Compatible state
  charge : divergence state = b v

@[ext] theorem Configuration.ext {b : Vertex n → Scalar} {v : Vertex n}
    {s t : Configuration b v} (h : ∀ e, s.state e = t.state e) : s = t := by
  cases s; cases t
  congr
  exact funext h

noncomputable def actState {v : Vertex n} (g : BoxGroup n) (s : LocalStates v) :
    LocalStates v := fun e => restrictGroup e.val g * s e

theorem actState_compatible {v : Vertex n} (g : BoxGroup n) (s : LocalStates v)
    (hs : Compatible s) : Compatible (actState g s) := by
  intro e e' f hf hf'
  simp only [actState, Support.H.mul_face, Pi.add_apply, restrictGroup_face]
  rw [hs e e' f hf hf']

theorem actState_divergence {v : Vertex n} (g : BoxGroup n) (s : LocalStates v)
    (hs : Compatible s) : divergence (actState g s) = divergence s := by
  classical
  obtain ⟨u,hu⟩ := (compatible_iff_extend s).mp hs
  have hc (e : IncidentEdges v) : Support.correction (localCycle e.val)
      (restrictGroup e.val g).face (s e).face =
        (Support.correction flowCycle g.face u).val e.val := by
    have heq : (s e).face = fun f : EdgeFaces e.val => u f.val := funext (hu e)
    rw [heq]
    simp only [Support.correction, Submodule.coe_smul, Submodule.coe_sum,
      Pi.smul_apply, Finset.sum_apply, smul_eq_mul, flowCycle, localCycle,
      restrictGroup_face]
    congr 1
    exact sum_subtype_zero (fun f : Face n => cycle f e.val ≠ 0)
      (fun f => omega (g.face f) (u f) * cycle f e.val)
      (fun f hf => by push Not at hf; simp only [hf,mul_zero])
  simp only [divergence, actState, Support.H.mul_flow, restrictGroup_flow,
    mul_add, Finset.sum_add_distrib]
  simp_rw [hc]
  rw [sum_incident, sum_incident]
  have hg := congrFun g.flow.property v
  have hb := congrFun (Support.correction flowCycle g.face u).property v
  simp only [Pi.zero_apply] at hg hb
  simp [hg,hb]

noncomputable def actConfiguration {b : Vertex n → Scalar} {v : Vertex n}
    (g : BoxGroup n) (s : Configuration b v) : Configuration b v where
  state := actState g s.state
  compatible := actState_compatible g s.state s.compatible
  charge := by rw [actState_divergence g s.state s.compatible, s.charge]

noncomputable instance {b : Vertex n → Scalar} {v : Vertex n} :
    MulAction (BoxGroup n) (Configuration b v) where
  smul := actConfiguration
  one_smul s := by
    apply Configuration.ext
    intro e
    change restrictGroup e.val (1 : BoxGroup n) * s.state e = s.state e
    simp only [map_one,one_mul]
  mul_smul g h s := by
    apply Configuration.ext
    intro e
    change restrictGroup e.val (g*h) * s.state e =
      restrictGroup e.val g * (restrictGroup e.val h * s.state e)
    simp only [map_mul,mul_assoc]

abbrev Atom (b : Vertex n → Scalar) := (Σ e : Edge n, LocalGroup e) ⊕
  (Σ v : Vertex n, Configuration b v)

noncomputable def actAtom {b : Vertex n → Scalar} (g : BoxGroup n) : Atom b → Atom b
  | .inl ⟨e,s⟩ => .inl ⟨e, restrictGroup e g * s⟩
  | .inr ⟨v,s⟩ => .inr ⟨v,g • s⟩

noncomputable instance {b : Vertex n → Scalar} : MulAction (BoxGroup n) (Atom b) where
  smul := actAtom
  one_smul x := by
    change actAtom 1 x = x
    cases x with
    | inl x => rcases x with ⟨e,s⟩; simp only [actAtom,map_one,one_mul]
    | inr x => rcases x with ⟨v,s⟩; simp only [actAtom,one_smul]
  mul_smul g h x := by
    change actAtom (g*h) x = actAtom g (actAtom h x)
    cases x with
    | inl x => rcases x with ⟨e,s⟩; simp only [actAtom,map_mul,mul_assoc]
    | inr x => rcases x with ⟨v,s⟩; simp only [actAtom,mul_smul]

end WitnessedSeparation.Grid

namespace WitnessedSeparation.Grid

open Support

variable {n : ℕ} {b : Vertex n → Scalar}

instance {v : Vertex n} : Finite (Configuration b v) :=
  Finite.of_injective (fun s : Configuration b v => s.state)
    (fun _s _t h => Configuration.ext (fun e => congrFun h e))

noncomputable instance {v : Vertex n} : Fintype (Configuration b v) := Fintype.ofFinite _

inductive AtomRelation (b : Vertex n → Scalar) : Symbol → Atom b → Atom b → Prop
  | ed (e : Edge n) (s : LocalGroup e) :
      AtomRelation b .Ed (.inl ⟨e,s⟩) (.inl ⟨e,s⟩)
  | cf (v : Vertex n) (s : Configuration b v) :
      AtomRelation b .Cf (.inr ⟨v,s⟩) (.inr ⟨v,s⟩)
  | eb (e : Edge n) (s t : LocalGroup e) :
      AtomRelation b .EB (.inl ⟨e,s⟩) (.inl ⟨e,t⟩)
  | vb (v : Vertex n) (s t : Configuration b v) :
      AtomRelation b .VB (.inr ⟨v,s⟩) (.inr ⟨v,t⟩)
  | inc (v : Vertex n) (s : Configuration b v) (e : IncidentEdges v) :
      AtomRelation b .I (.inr ⟨v,s⟩) (.inl ⟨e.val,s.state e⟩)
  | z (e : Edge n) (s t : LocalGroup e) (δ : Scalar) (h : (s⁻¹*t).flow = δ) :
      AtomRelation b (.Z δ) (.inl ⟨e,s⟩) (.inl ⟨e,t⟩)

theorem AtomRelation.map (g : BoxGroup n) {r : Symbol} {x y : Atom b}
    (h : AtomRelation b r x y) : AtomRelation b r (g • x) (g • y) := by
  cases h with
  | ed e s => exact .ed e _
  | cf v s => exact .cf v _
  | eb e s t => exact .eb e _ _
  | vb v s t => exact .vb v _ _
  | inc v s e => exact .inc v (g • s) e
  | z e s t δ h =>
    apply AtomRelation.z
    simpa only [mul_inv_rev, mul_assoc, inv_mul_cancel_left] using h

theorem AtomRelation.map_iff (g : BoxGroup n) (r : Symbol) (x y : Atom b) :
    AtomRelation b r (g • x) (g • y) ↔ AtomRelation b r x y := by
  constructor
  · intro h
    simpa only [inv_smul_smul] using h.map g⁻¹
  · exact fun h => h.map g

noncomputable def atomInput (b : Vertex n → Scalar) : Input (Atom b) :=
  ⟨fun r x y => @decide (AtomRelation b r x y) (Classical.propDecidable _)⟩

end WitnessedSeparation.Grid

namespace WitnessedSeparation.Grid

variable {n : ℕ}

theorem head_ne_tail (e : Edge n) : head e ≠ tail e := by
  rcases e with ⟨i,j,k⟩ | (⟨i,j,k⟩ | ⟨i,j,k⟩)
  all_goals simp only [head,tail]
  · intro h
    have hu := congrArg (fun v : Vertex n => v.1.val) h
    simp only [Fin.val_succ,Fin.val_castSucc] at hu
    omega
  · intro h
    have hu := congrArg (fun v : Vertex n => v.2.1.val) h
    simp only [Fin.val_succ,Fin.val_castSucc] at hu
    omega
  · intro h
    have hu := congrArg (fun v : Vertex n => v.2.2.val) h
    simp only [Fin.val_succ,Fin.val_castSucc] at hu
    omega

theorem sum_boundary (z : Edge n → Scalar) : ∑ v, boundary z v = 0 := by
  classical
  simp only [boundary, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply,
    Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro e _
  simp [mul_sub,Finset.sum_sub_distrib,← Finset.mul_sum]

def edgeAxis : Edge n → Fin 3
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr _) => 2

theorem head_injective_on_axis {e e' : Edge n}
    (ha : edgeAxis e = edgeAxis e') (hh : head e = head e') : e = e' := by
  rcases e with ⟨i,j,k⟩ | (⟨i,j,k⟩ | ⟨i,j,k⟩)
  all_goals rcases e' with ⟨i',j',k'⟩ | (⟨i',j',k'⟩ | ⟨i',j',k'⟩)
  all_goals simp_all [edgeAxis,head]

theorem tail_injective_on_axis {e e' : Edge n}
    (ha : edgeAxis e = edgeAxis e') (hh : tail e = tail e') : e = e' := by
  rcases e with ⟨i,j,k⟩ | (⟨i,j,k⟩ | ⟨i,j,k⟩)
  all_goals rcases e' with ⟨i',j',k'⟩ | (⟨i',j',k'⟩ | ⟨i',j',k'⟩)
  all_goals simp_all [edgeAxis,tail]

theorem exists_head_or_tail (hn : 1 ≤ n) (v : Vertex n) :
    ∃ e : Edge n, head e = v ∨ tail e = v := by
  rcases v with ⟨i,j,k⟩
  by_cases hi : i.val = 0
  · refine ⟨ex ⟨0,by omega⟩ j k, Or.inr ?_⟩
    simp only [ex,tail,Prod.mk.injEq, and_true]
    apply Fin.ext
    exact hi.symm
  · refine ⟨ex ⟨i.val-1,by omega⟩ j k, Or.inl ?_⟩
    simp only [ex,head,Prod.mk.injEq,and_true]
    apply Fin.ext
    simp only [Fin.val_succ]
    omega

theorem degree_le_six (v : Vertex n) :
    Fintype.card {e : Edge n // head e = v ∨ tail e = v} ≤ 6 := by
  classical
  let f : {e : Edge n // head e = v ∨ tail e = v} → Fin 3 × Bool :=
    fun e => (edgeAxis e.val, decide (head e.val = v))
  have hf : Function.Injective f := by
    intro e e' heq
    have ha : edgeAxis e.val = edgeAxis e'.val := congrArg Prod.fst heq
    have hb : decide (head e.val = v) = decide (head e'.val = v) := congrArg Prod.snd heq
    apply Subtype.ext
    by_cases he : head e.val = v
    · have he' : head e'.val = v := by simpa only [he,decide_true,true_eq_decide_iff] using hb
      exact head_injective_on_axis ha (he.trans he'.symm)
    · have he' : head e'.val ≠ v := by simpa only [he,decide_false,false_eq_decide_iff] using hb
      exact tail_injective_on_axis ha
        ((e.property.resolve_left he).trans (e'.property.resolve_left he').symm)
  have h := Fintype.card_le_of_injective f hf
  simpa using h

end WitnessedSeparation.Grid

namespace WitnessedSeparation.Grid

noncomputable instance {n : ℕ} (e : Edge n) : Fintype (LocalGroup e) := Fintype.ofFinite _

noncomputable instance {n : ℕ} {b : Vertex n → Scalar} : Fintype (Atom b) := Fintype.ofFinite _

end WitnessedSeparation.Grid


namespace WitnessedSeparation

namespace Input

variable {A B : Type} [Fintype A] [Fintype B]

abbrev Edge (S : Input A) := {y : A // S.rel .Ed y y = true}

abbrev Config (S : Input A) := {a : A // S.rel .Cf a a = true}

instance (S : Input A) : Fintype S.Edge := inferInstanceAs (Fintype {_y // _})

instance (S : Input A) : Fintype S.Config := inferInstanceAs (Fintype {_a // _})

instance [DecidableEq A] (S : Input A) : DecidableEq S.Edge := inferInstanceAs (DecidableEq {_y // _})

instance [DecidableEq A] (S : Input A) : DecidableEq S.Config := inferInstanceAs (DecidableEq {_a // _})

def coefficient (S : Input A) (y : S.Edge) (a : S.Config) : Scalar :=
  ∑ x : S.Edge, if S.rel .I a x then
    ∑ δ : Scalar, if S.rel (.Z δ) y x then δ else 0
    else 0

def incident (S : Input A) (t : S.Config) (y : S.Edge) : Prop :=
  ∃ a : S.Config, S.rel .VB t a = true ∧
    ∃ x : S.Edge, S.rel .I a x = true ∧ S.rel .EB y x = true

def normalized (S : Input A) (lambda : S.Config → Scalar) : Prop :=
  ∀ t : S.Config, (∑ a : S.Config, if S.rel .VB t a then lambda a else 0) = 1

def consistent (S : Input A) (lambda : S.Config → Scalar) (mu : S.Edge → Scalar) : Prop :=
  ∀ (t : S.Config) (y : S.Edge), S.incident t y →
    mu y = ∑ a : S.Config, if S.rel .VB t a then lambda a * S.coefficient y a else 0

def query (S : Input A) : Prop :=
  ∃ (lambda : S.Config → Scalar) (mu : S.Edge → Scalar), S.normalized lambda ∧ S.consistent lambda mu

structure Iso (S : Input A) (T : Input B) extends A ≃ B where
  rel_eq : ∀ r x y, T.rel r (toEquiv x) (toEquiv y) = S.rel r x y

namespace Iso

variable {S : Input A} {T : Input B} (e : S.Iso T)

def edgeEquiv : S.Edge ≃ T.Edge :=
  e.toEquiv.subtypeEquiv (fun a => by simp only [e.rel_eq])

def configEquiv : S.Config ≃ T.Config :=
  e.toEquiv.subtypeEquiv (fun a => by simp only [e.rel_eq])

omit [Fintype A] [Fintype B] in
@[simp] theorem edgeEquiv_val (x : S.Edge) : (e.edgeEquiv x).val = e.toEquiv x := rfl

omit [Fintype A] [Fintype B] in
@[simp] theorem configEquiv_val (x : S.Config) : (e.configEquiv x).val = e.toEquiv x := rfl

@[simp] theorem coefficient_eq (y : S.Edge) (a : S.Config) :
    T.coefficient (e.edgeEquiv y) (e.configEquiv a) = S.coefficient y a := by
  unfold coefficient
  symm
  apply Fintype.sum_equiv e.edgeEquiv
  intro x
  simp [edgeEquiv, configEquiv, e.rel_eq]

omit [Fintype A] [Fintype B] in
@[simp] theorem incident_eq (t : S.Config) (y : S.Edge) :
    T.incident (e.configEquiv t) (e.edgeEquiv y) ↔ S.incident t y := by
  unfold incident
  constructor
  · rintro ⟨a, ha, x, hx, hy⟩
    refine ⟨e.configEquiv.symm a, ?_, e.edgeEquiv.symm x, ?_, ?_⟩
    all_goals
      have heqa : e.toEquiv (e.configEquiv.symm a).val = a.val :=
        congrArg Subtype.val (e.configEquiv.apply_symm_apply a)
      have heqx : e.toEquiv (e.edgeEquiv.symm x).val = x.val :=
        congrArg Subtype.val (e.edgeEquiv.apply_symm_apply x)
      first
      | simpa only [configEquiv_val, edgeEquiv_val, ← heqa, ← heqx, e.rel_eq] using ha
      | simpa only [configEquiv_val, edgeEquiv_val, ← heqa, ← heqx, e.rel_eq] using hx
      | simpa only [configEquiv_val, edgeEquiv_val, ← heqa, ← heqx, e.rel_eq] using hy
  · rintro ⟨a, ha, x, hx, hy⟩
    refine ⟨e.configEquiv a, ?_, e.edgeEquiv x, ?_, ?_⟩
    · simpa only [configEquiv_val, e.rel_eq] using ha
    · simpa only [configEquiv_val, edgeEquiv_val, e.rel_eq] using hx
    · simpa only [edgeEquiv_val, e.rel_eq] using hy

def symm : T.Iso S where
  toEquiv := e.toEquiv.symm
  rel_eq r x y := by
    simpa only [Equiv.apply_symm_apply] using
      (e.rel_eq r (e.toEquiv.symm x) (e.toEquiv.symm y)).symm

include e in
theorem query_map : S.query → T.query := by
  rintro ⟨lambda, mu, hn, hc⟩
  refine ⟨lambda ∘ e.configEquiv.symm, mu ∘ e.edgeEquiv.symm, ?_, ?_⟩
  · intro t
    obtain ⟨t, rfl⟩ := e.configEquiv.surjective t
    calc
      (∑ a : T.Config, if T.rel .VB (e.configEquiv t) a then
        (lambda ∘ e.configEquiv.symm) a else 0) =
          ∑ a : S.Config, if S.rel .VB t a then lambda a else 0 := by
            symm
            apply Fintype.sum_equiv e.configEquiv
            intro a
            simp [configEquiv, e.rel_eq]
      _ = 1 := hn t
  · intro t y ht
    obtain ⟨t, rfl⟩ := e.configEquiv.surjective t
    obtain ⟨y, rfl⟩ := e.edgeEquiv.surjective y
    have hi : S.incident t y := (e.incident_eq t y).mp ht
    simp only [Function.comp_apply, Equiv.symm_apply_apply]
    calc
      mu y = ∑ a : S.Config, if S.rel .VB t a then lambda a * S.coefficient y a
        else 0 := hc t y hi
      _ = ∑ a : T.Config, if T.rel .VB (e.configEquiv t) a then
          (lambda ∘ e.configEquiv.symm) a * T.coefficient (e.edgeEquiv y) a else 0 := by
        apply Fintype.sum_equiv e.configEquiv
        intro a
        simp [configEquiv_val, e.rel_eq]

end Iso

theorem query_invariant {S : Input A} {T : Input B} (e : S.Iso T) :
    S.query ↔ T.query := ⟨e.query_map, e.symm.query_map⟩

end Input

end WitnessedSeparation



namespace WitnessedSeparation.Grid

open Support

variable {n : ℕ} {b : Vertex n → Scalar}

noncomputable def actionIso (g : BoxGroup n) : (atomInput b).Iso (atomInput b) where
  toFun x := g • x
  invFun x := g⁻¹ • x
  left_inv := inv_smul_smul g
  right_inv := smul_inv_smul g
  rel_eq := by
    intro r x y
    exact congrArg (fun p => @decide p (Classical.propDecidable p))
      (propext (AtomRelation.map_iff g r x y))

def zeroEdgeAtom (b : Vertex n → Scalar) (e : Edge n) : Atom b := .inl ⟨e,1⟩

@[simp] theorem central_fix_zeroEdgeAtom_iff (k : FlowSpace n) (e : Edge n) :
    Support.H.central flowCycle k • zeroEdgeAtom b e = zeroEdgeAtom b e ↔ k.val e = 0 := by
  change (Sum.inl ⟨e,restrictGroup e (Support.H.central flowCycle k) * 1⟩ : Atom b) =
    (Sum.inl ⟨e,(1 : LocalGroup e)⟩ : Atom b) ↔ _
  simp only [mul_one, Sum.inl.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and]
  constructor
  · intro h
    exact congrArg Support.H.flow h
  · intro h
    apply Support.H.ext
    · rfl
    · exact h

abbrev CentralGroup (n : ℕ) := Multiplicative (FlowSpace n)

def centralHom : CentralGroup n →* BoxGroup n where
  toFun k := Support.H.central flowCycle k.toAdd
  map_one' := rfl
  map_mul' k l := (Support.H.central_mul flowCycle k.toAdd l.toAdd).symm

noncomputable instance : MulAction (CentralGroup n) (Atom b) :=
  MulAction.compHom _ centralHom

@[simp] theorem central_smul_atom (k : CentralGroup n) (x : Atom b) :
    k • x = Support.H.central flowCycle k.toAdd • x := rfl

theorem edge_support_tuple {X : Type*} [MulAction (BoxGroup n) X]
    (T : Finset (Edge n)) (x : X)
    (hx : ∀ k : FlowSpace n, (∀ e ∈ T, k.val e = 0) →
      Support.H.central flowCycle k • x = x) :
    ∃ alpha : Fin T.card → Atom b, ∀ k : CentralGroup n,
      (∀ i, k • alpha i = alpha i) → centralHom k • x = x := by
  classical
  let alpha (i : Fin T.card) : Atom b := zeroEdgeAtom b ((T.equivFin).symm i).val
  refine ⟨alpha,?_⟩
  intro k hk
  apply hx k.toAdd
  intro e he
  let i : Fin T.card := T.equivFin ⟨e,he⟩
  have hi : ((T.equivFin).symm i).val = e := by simp [i]
  have hfix := hk i
  change Support.H.central flowCycle k.toAdd •
      zeroEdgeAtom b ((T.equivFin).symm i).val = _ at hfix
  rw [central_fix_zeroEdgeAtom_iff] at hfix
  simpa only [hi] using hfix

end WitnessedSeparation.Grid



namespace WitnessedSeparation.Grid

noncomputable section

open Support

variable {n : ℕ} {b : Vertex n → Scalar}

@[simp] theorem atomInput_rel_true (r : Symbol) (x y : Atom b) :
    (atomInput b).rel r x y = true ↔ AtomRelation b r x y := by
  simp [atomInput]

def queryEdge (e : Edge n) (g : LocalGroup e) : (atomInput b).Edge :=
  ⟨.inl ⟨e,g⟩,by simp only [atomInput_rel_true]; exact .ed e g⟩

def queryConfig (v : Vertex n) (s : Configuration b v) : (atomInput b).Config :=
  ⟨.inr ⟨v,s⟩,by simp only [atomInput_rel_true]; exact .cf v s⟩

theorem exists_queryEdge (y : (atomInput b).Edge) :
    ∃ (e : Edge n) (g : LocalGroup e), y = queryEdge e g := by
  rcases y with ⟨y,hy⟩
  have h := (atomInput_rel_true .Ed y y).mp hy
  cases h with
  | ed e g => exact ⟨e,g,rfl⟩

theorem exists_queryConfig (a : (atomInput b).Config) :
    ∃ (v : Vertex n) (s : Configuration b v), a = queryConfig v s := by
  rcases a with ⟨a,ha⟩
  have h := (atomInput_rel_true .Cf a a).mp ha
  cases h with
  | cf v s => exact ⟨v,s,rfl⟩

@[simp] theorem queryEdge_eq {e e' : Edge n} {g : LocalGroup e} {g' : LocalGroup e'} :
    queryEdge (b := b) e g = queryEdge e' g' ↔ (⟨e,g⟩ : Σ e, LocalGroup e) = ⟨e',g'⟩ := by
  simp [queryEdge,Subtype.ext_iff]

@[simp] theorem queryConfig_eq {v v' : Vertex n} {s : Configuration b v}
    {s' : Configuration b v'} :
    queryConfig v s = queryConfig v' s' ↔ (⟨v,s⟩ : Σ v, Configuration b v) = ⟨v',s'⟩ := by
  simp [queryConfig,Subtype.ext_iff]

def queryEdgeEquiv : (Σ e : Edge n, LocalGroup e) ≃ (atomInput b).Edge :=
  Equiv.ofBijective (fun x => queryEdge x.1 x.2) ⟨by
    rintro ⟨e,g⟩ ⟨e',g'⟩ h
    exact queryEdge_eq.mp h,
    fun y => by obtain ⟨e,g,rfl⟩ := exists_queryEdge y; exact ⟨⟨e,g⟩,rfl⟩⟩

def queryConfigEquiv : (Σ v : Vertex n, Configuration b v) ≃ (atomInput b).Config :=
  Equiv.ofBijective (fun x => queryConfig x.1 x.2) ⟨by
    rintro ⟨v,s⟩ ⟨v',s'⟩ h
    exact queryConfig_eq.mp h,
    fun a => by obtain ⟨v,s,rfl⟩ := exists_queryConfig a; exact ⟨⟨v,s⟩,rfl⟩⟩

@[simp] theorem rel_vb (v w : Vertex n) (s : Configuration b v) (t : Configuration b w) :
    (atomInput b).rel .VB (queryConfig v s) (queryConfig w t) = true ↔ v = w := by
  rw [atomInput_rel_true]
  constructor
  · intro h
    cases h
    rfl
  · rintro rfl
    exact .vb v s t

@[simp] theorem rel_eb (e f : Edge n) (g : LocalGroup e) (h : LocalGroup f) :
    (atomInput b).rel .EB (queryEdge (b := b) e g) (queryEdge (b := b) f h) = true ↔ e = f := by
  rw [atomInput_rel_true]
  constructor
  · intro h
    cases h
    rfl
  · rintro rfl
    exact .eb e g h

@[simp] theorem rel_inc (v : Vertex n) (s : Configuration b v) (e : Edge n)
    (g : LocalGroup e) :
    (atomInput b).rel .I (queryConfig v s) (queryEdge (b := b) e g) = true ↔
      ∃ h : incident v e, s.state ⟨e,h⟩ = g := by
  rw [atomInput_rel_true]
  constructor
  · intro h
    cases h with
    | inc v s e => exact ⟨e.property,rfl⟩
  · rintro ⟨h,rfl⟩
    exact .inc v s ⟨e,h⟩

@[simp] theorem rel_z_same (e : Edge n) (g h : LocalGroup e) (d : Scalar) :
    (atomInput b).rel (.Z d) (queryEdge (b := b) e g) (queryEdge (b := b) e h) = true ↔ (g⁻¹*h).flow = d := by
  rw [atomInput_rel_true]
  constructor
  · intro h
    cases h with
    | z e g h d hd => exact hd
  · intro hd
    exact .z e g h d hd

theorem rel_z_edge (e f : Edge n) (g : LocalGroup e) (h : LocalGroup f) (d : Scalar)
    (hz : (atomInput b).rel (.Z d) (queryEdge (b := b) e g) (queryEdge (b := b) f h) = true) : e = f := by
  rw [atomInput_rel_true] at hz
  cases hz
  rfl

@[simp] theorem epsilon_head (e : Edge n) : epsilon (head e) e = 1 := by
  simp [epsilon,Ne.symm (head_ne_tail e)]

@[simp] theorem epsilon_tail (e : Edge n) : epsilon (tail e) e = -1 := by
  simp [epsilon,head_ne_tail e]

theorem epsilon_sq (v : Vertex n) (e : IncidentEdges v) : epsilon v e.val ^ 2 = 1 := by
  rcases e with ⟨e,he⟩
  rcases he with h | h
  · subst v; simp
  · subst v; simp

def someConfiguration (hn : 1 ≤ n) (b : Vertex n → Scalar) (v : Vertex n) : Configuration b v := by
  classical
  let e : IncidentEdges v := ⟨(exists_head_or_tail hn v).choose,(exists_head_or_tail hn v).choose_spec⟩
  let states : LocalStates v := fun f => ⟨0,if f = e then epsilon v e.val * b v else 0⟩
  refine ⟨states,?_,?_⟩
  · intro f f' d hd hd'
    rfl
  · dsimp [divergence,states]
    simp only [mul_ite,mul_zero]
    rw [Finset.sum_ite_eq' Finset.univ e]
    simp only [Finset.mem_univ,ite_true]
    rw [← mul_assoc,← pow_two,epsilon_sq,one_mul]

def zeroConfiguration (v : Vertex n) : Configuration (0 : Vertex n → Scalar) v where
  state := fun _ => 1
  compatible := by intro e e' f hf hf'; rfl
  charge := by simp [divergence,Support.H.one_flow]

theorem sum_queryEdges {M : Type*} [AddCommMonoid M] (f : (atomInput b).Edge → M) :
    (∑ y, f y) = ∑ e, ∑ g, f (queryEdge e g) := by
  rw [← (queryEdgeEquiv (b := b)).sum_comp f,Fintype.sum_sigma]
  rfl

theorem sum_queryConfigs {M : Type*} [AddCommMonoid M] (f : (atomInput b).Config → M) :
    (∑ a, f a) = ∑ v, ∑ t, f (queryConfig v t) := by
  rw [← (queryConfigEquiv (b := b)).sum_comp f,Fintype.sum_sigma]
  rfl

theorem zsum_same (e : Edge n) (g h : LocalGroup e) :
    (∑ d : Scalar, if (atomInput b).rel (.Z d)
      (queryEdge (b := b) e g) (queryEdge (b := b) e h) then d else 0) = (g⁻¹*h).flow := by
  simp only [rel_z_same]
  simp

theorem zsum_ne (e f : Edge n) (g : LocalGroup e) (h : LocalGroup f) (hne : e ≠ f) :
    (∑ d : Scalar, if (atomInput b).rel (.Z d)
      (queryEdge (b := b) e g) (queryEdge (b := b) f h) then d else 0) = 0 := by
  apply Finset.sum_eq_zero
  intro d _
  have hh : ¬(atomInput b).rel (.Z d)
      (queryEdge (b := b) e g) (queryEdge (b := b) f h) = true := fun hd =>
    hne (rel_z_edge e f g h d hd)
  simp [hh]

theorem coefficient_incident (v : Vertex n) (s : Configuration b v)
    (e : Edge n) (g : LocalGroup e) (he : incident v e) :
    (atomInput b).coefficient (queryEdge e g) (queryConfig v s) =
      (g⁻¹ * s.state ⟨e,he⟩).flow := by
  classical
  unfold Input.coefficient
  rw [sum_queryEdges,Finset.sum_eq_single e]
  · simp only [zsum_same,rel_inc]
    have hiff : ∀ h : LocalGroup e,
        (∃ he : incident v e, s.state ⟨e,he⟩ = h) ↔ s.state ⟨e,he⟩ = h := by
      intro h
      exact ⟨fun ⟨_,hh⟩ => hh,fun hh => ⟨he,hh⟩⟩
    simp only [hiff]
    simp
  · intro f _ hfe
    apply Finset.sum_eq_zero
    intro h _
    simp only [zsum_ne e f g h hfe.symm,ite_self]
  · simp

theorem query_incident_iff (v : Vertex n) (s : Configuration b v)
    (e : Edge n) (g : LocalGroup e) :
    (atomInput b).incident (queryConfig v s) (queryEdge e g) ↔ incident v e := by
  constructor
  · rintro ⟨a,hvb,x,hI,hEB⟩
    obtain ⟨w,t,rfl⟩ := exists_queryConfig a
    obtain ⟨f,h,rfl⟩ := exists_queryEdge x
    have hw : v = w := (rel_vb v w s t).mp hvb
    have hf : e = f := (rel_eb e f g h).mp hEB
    subst w; subst f
    exact ((rel_inc v t e h).mp hI).choose
  · intro he
    refine ⟨queryConfig v s,?_,queryEdge e (s.state ⟨e,he⟩),?_,?_⟩
    · exact (rel_vb _ _ _ _).mpr rfl
    · exact (rel_inc _ _ _ _).mpr ⟨he,rfl⟩
    · exact (rel_eb _ _ _ _).mpr rfl

theorem sum_block (v : Vertex n) (s : Configuration b v) (f : (atomInput b).Config → Scalar) :
    (∑ a : (atomInput b).Config, if (atomInput b).rel .VB (queryConfig v s) a then f a else 0) =
      ∑ t : Configuration b v, f (queryConfig v t) := by
  classical
  rw [sum_queryConfigs]
  simp only [rel_vb]
  rw [Finset.sum_eq_single v]
  · simp
  · intro w _ hw
    simp [Ne.symm hw]
  · simp

theorem block_normalized (hn : 1 ≤ n) (lambda : (atomInput b).Config → Scalar)
    (hl : (atomInput b).normalized lambda) (v : Vertex n) :
    (∑ t : Configuration b v, lambda (queryConfig v t)) = 1 := by
  have h := hl (queryConfig v (someConfiguration hn b v))
  rw [sum_block] at h
  exact h

theorem flow_query_eq (hn : 1 ≤ n) (lambda : (atomInput b).Config → Scalar)
    (mu : (atomInput b).Edge → Scalar) (h : (atomInput b).consistent lambda mu)
    (v : Vertex n) (e : IncidentEdges v) :
    mu (queryEdge e.val 1) = ∑ t : Configuration b v, lambda (queryConfig v t) * (t.state e).flow := by
  have hh := h (queryConfig v (someConfiguration hn b v)) (queryEdge e.val 1)
    ((query_incident_iff _ _ _ _).mpr e.property)
  rw [sum_block] at hh
  simpa only [coefficient_incident v _ e.val 1 e.property,inv_one,one_mul] using hh

theorem query_implies_total_charge_zero (hn : 1 ≤ n) (hq : (atomInput b).query) :
    (∑ v, b v) = 0 := by
  classical
  obtain ⟨lambda,mu,hl,hm⟩ := hq
  let z : Edge n → Scalar := fun e => mu (queryEdge e 1)
  have hz : boundary z = b := by
    funext v
    rw [← sum_incident]
    change (∑ e : IncidentEdges v, epsilon v e.val * mu (queryEdge e.val 1)) = b v
    simp_rw [flow_query_eq hn lambda mu hm,Finset.mul_sum]
    rw [Finset.sum_comm]
    calc
      (∑ t : Configuration b v, ∑ e : IncidentEdges v,
        epsilon v e.val * (lambda (queryConfig v t) * (t.state e).flow)) =
        ∑ t : Configuration b v, lambda (queryConfig v t) * divergence t.state := by
          apply Finset.sum_congr rfl
          intro t _
          simp only [divergence,Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro e _
          ring
      _ = ∑ t : Configuration b v, lambda (queryConfig v t) * b v := by
          simp only [Configuration.charge]
      _ = b v := by rw [← Finset.sum_mul,block_normalized hn lambda hl,one_mul]
  rw [← hz]
  exact sum_boundary z

def zeroWeight (a : (atomInput (0 : Vertex n → Scalar)).Config) : Scalar := by
  classical
  exact match a.val with
  | .inl _ => 0
  | .inr ⟨v,t⟩ => if t = zeroConfiguration v then 1 else 0

def zeroMu (y : (atomInput (0 : Vertex n → Scalar)).Edge) : Scalar :=
  match y.val with
  | .inl ⟨_,g⟩ => -g.flow
  | .inr _ => 0

theorem query_zero_charge : (atomInput (0 : Vertex n → Scalar)).query := by
  classical
  refine ⟨zeroWeight,zeroMu,?_,?_⟩
  · intro a
    obtain ⟨v,t,rfl⟩ := exists_queryConfig a
    rw [sum_block]
    simp [zeroWeight,queryConfig]
  · intro a y hi
    obtain ⟨v,t,rfl⟩ := exists_queryConfig a
    obtain ⟨e,g,rfl⟩ := exists_queryEdge y
    have he : incident v e := (query_incident_iff v t e g).mp hi
    rw [sum_block]
    change -g.flow = ∑ t' : Configuration (0 : Vertex n → Scalar) v,
      (if t' = zeroConfiguration v then 1 else 0) *
        (atomInput (0 : Vertex n → Scalar)).coefficient (queryEdge e g) (queryConfig v t')
    simp only [ite_mul,one_mul,zero_mul]
    rw [Finset.sum_ite_eq' Finset.univ (zeroConfiguration v)]
    simp only [Finset.mem_univ,ite_true,coefficient_incident v _ e g he,
      zeroConfiguration, mul_one,Support.H.inv_flow]

theorem opposite_answers (hn : 1 ≤ n) (vstar : Vertex n) :
    (atomInput (0 : Vertex n → Scalar)).query ∧
      ¬ (atomInput (Pi.single vstar (1 : Scalar))).query := by
  refine ⟨query_zero_charge,?_⟩
  intro h
  have hh := query_implies_total_charge_zero hn h
  simp at hh

end

end WitnessedSeparation.Grid

end OAI
