import OAI.Combinatorics.PerfectMatching.Polytope

namespace OAI

/-!
Active face spaces, their codimension bounds, and local radial extension.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

namespace LooplessGraph

/-- Restrict the ambient vector space to the genuinely positive edge coordinates. -/
def positiveExtension (x : E → ℝ) : ({e // 0<x e} → ℝ) →ₗ[ℝ] (E → ℝ) := by
  classical
  exact {
    toFun := fun u e => if h : 0<x e then u ⟨e,h⟩ else 0
    map_add' := by intro u v; ext e; by_cases h : 0<x e <;> simp [h]
    map_smul' := by intro a u; ext e; by_cases h : 0<x e <;> simp [h] }

omit [Fintype E] [DecidableEq E] in
@[simp] theorem positiveExtension_pos (x : E → ℝ) (u : {e // 0<x e} → ℝ)
    (e : {e // 0<x e}) : positiveExtension x u e.val=u e := by
  simp [positiveExtension,e.property]

omit [Fintype E] [DecidableEq E] in
@[simp] theorem positiveExtension_zero (x : E → ℝ) (u : {e // 0<x e} → ℝ)
    {e : E} (he : x e=0) : positiveExtension x u e=0 := by
  simp [positiveExtension,he]

def degreeLinear (G : LooplessGraph V E) : (E → ℝ) →ₗ[ℝ] (V → ℝ) where
  toFun := G.degree
  map_add' := by
    intro u v
    ext w
    simpa using G.degree_linear u v 1 1 w
  map_smul' := by
    intro a u
    ext w
    simp only [degree,Pi.smul_apply,smul_eq_mul,RingHom.id_apply,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    split <;> simp

def cutLinear (G : LooplessGraph V E) (S : Finset V) : (E → ℝ) →ₗ[ℝ] ℝ where
  toFun := fun u => G.cutMass u S
  map_add' := by intro u v; simpa using G.cutMass_linear u v 1 1 S
  map_smul' := by intro a u; simp [cutMass,Finset.mul_sum]

/-- The exact active degree and odd-cut kernel, on the positive edge support. -/
def faceSpace (G : LooplessGraph V E) (x : E → ℝ) : Submodule ℝ ({e // 0<x e} → ℝ) where
  carrier := {u | G.degreeLinear (positiveExtension x u)=0 ∧
    ∀ S : Finset V, Odd S.card → G.cutMass x S=1 → G.cutLinear S (positiveExtension x u)=0}
  zero_mem' := by simp
  add_mem' := by
    intro u v hu hv
    refine ⟨by simp only [map_add,hu.1,hv.1,add_zero],?_⟩
    intro S hS ht
    simp only [map_add,hu.2 S hS ht,hv.2 S hS ht,add_zero]
  smul_mem' := by
    intro a u hu
    refine ⟨by simp only [map_smul,hu.1,smul_zero],?_⟩
    intro S hS ht
    simp only [map_smul,hu.2 S hS ht,smul_zero]

def faceCodimension (G : LooplessGraph V E) (x : E → ℝ) : ℕ :=
  Module.finrank ℝ (({e // 0<x e} → ℝ) ⧸ G.faceSpace x)

omit [DecidableEq E] in
 theorem faceCodimension_no_tight (G : LooplessGraph V E) {x : E → ℝ}
    (heven : Even (Fintype.card V))
    (hnt : ¬∃ S : Finset V, Odd S.card ∧ 3≤S.card ∧ 3≤Sᶜ.card ∧ G.cutMass x S=1) :
    G.faceCodimension x ≤ Fintype.card V := by
  classical
  let F := G.degreeLinear.comp (positiveExtension x)
  have hk : F.ker ≤ G.faceSpace x := by
    intro u hu
    have hd : G.degreeLinear (positiveExtension x u)=0 := hu
    refine ⟨hd,?_⟩
    exact G.trivial_tight_cut_preserved heven hnt _ (congrFun hd)
  simpa [faceCodimension] using quotient_finrank_le_of_ker_le (G.faceSpace x) F hk

omit [DecidableEq E] in
 theorem faceSpace_eventually_line (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x ∈ G.constraintPolytope) {u : {e // 0<x e} → ℝ} (hu : u ∈ G.faceSpace x) :
    ∀ᶠ t : ℝ in 𝓝 0, x+t • positiveExtension x u ∈ G.constraintPolytope := by
  exact G.constraint_eventually_line hx _ (fun e he => positiveExtension_zero x u he)
    (congrFun hu.1) hu.2

omit [Fintype V] [DecidableEq E] in
 theorem faceSpace_of_eventually_line (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x ∈ G.constraintPolytope) {u : {e // 0<x e} → ℝ}
    (hu : ∀ᶠ t : ℝ in 𝓝 0, x+t • positiveExtension x u ∈ G.constraintPolytope) :
    u ∈ G.faceSpace x := by
  have hu' : ∀ᶠ t : ℝ in 𝓝 0, x+(-t) • positiveExtension x u ∈ G.constraintPolytope := by
    have hc : Tendsto (fun t : ℝ => -t) (𝓝 0) (𝓝 0) := by simpa using continuous_neg.tendsto (0:ℝ)
    exact hc.eventually hu
  have hh : ∀ᶠ t : ℝ in 𝓝[>] 0,
      (x+t • positiveExtension x u ∈ G.constraintPolytope ∧
        x+(-t) • positiveExtension x u ∈ G.constraintPolytope) ∧ 0<t :=
    ((hu.and hu').filter_mono nhdsWithin_le_nhds).and eventually_mem_nhdsWithin
  obtain ⟨a,⟨ha,hna⟩,ha0⟩ := hh.exists
  refine ⟨?_,?_⟩
  · ext v
    have he := G.degree_linear x (positiveExtension x u) 1 a v
    simp only [one_smul,one_mul,hx.2.1,ha.2.1] at he
    change G.degree (positiveExtension x u) v=0
    nlinarith
  · intro S hS ht
    have he := G.cutMass_linear x (positiveExtension x u) 1 a S
    have he' := G.cutMass_linear x (positiveExtension x u) 1 (-a) S
    simp only [one_smul,one_mul,ht] at he he'
    have hp := ha.2.2 S hS
    have hn := hna.2.2 S hS
    change G.cutMass (positiveExtension x u) S=0
    nlinarith


abbrev sideMarginal (G : LooplessGraph V E) (x : E → ℝ) (S : Finset V) :
    {e // G.left e ∈ S ∨ G.right e ∈ S} → ℝ := fun e => x e.val

def sideRestriction (G : LooplessGraph V E) (x : E → ℝ) (S : Finset V) :
    ({e // 0<x e} → ℝ) →ₗ[ℝ] ({e // 0<G.sideMarginal x S e} → ℝ) where
  toFun := fun u e => u ⟨e.val.val,e.property⟩
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
 theorem positiveExtension_side (G : LooplessGraph V E) (x : E → ℝ) (S : Finset V)
    (u : {e // 0<x e} → ℝ) (e : {e // G.left e ∈ S ∨ G.right e ∈ S}) :
    positiveExtension (G.sideMarginal x S) (G.sideRestriction x S u) e =
      positiveExtension x u e.val := by
  rfl

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
 theorem sideMarginal_line (G : LooplessGraph V E) (x : E → ℝ) (S : Finset V)
    (u : {e // 0<x e} → ℝ) (t : ℝ) :
    G.sideMarginal (x+t • positiveExtension x u) S = G.sideMarginal x S +
      t • positiveExtension (G.sideMarginal x S) (G.sideRestriction x S u) := by
  rfl

/-- Pullbacks of both contraction face spaces preserve every original active cut,
including cuts crossing the chosen tight cut. This is the substantive coupling step. -/
theorem faceSpace_of_side_spaces (G : LooplessGraph V E) {x : E → ℝ}
    (heven : Even (Fintype.card V)) (hx : x ∈ G.constraintPolytope)
    (S : Finset V) (hS : Odd S.card) (ht : G.cutMass x S=1)
    {u : {e // 0<x e} → ℝ}
    (h1 : G.sideRestriction x S u ∈ (G.onSide S).faceSpace (G.sideMarginal x S))
    (h2 : G.sideRestriction x Sᶜ u ∈ (G.onSide Sᶜ).faceSpace (G.sideMarginal x Sᶜ)) :
    u ∈ G.faceSpace x := by
  have hc := odd_compl_of_even heven hS
  have htc : G.cutMass x Sᶜ=1 := by simpa only [cutMass,cut_compl] using ht
  have hx1 := G.restriction_mem_constraints hx S hS ht
  have hx2 := G.restriction_mem_constraints hx Sᶜ hc htc
  have hv1 : Even (Fintype.card (Option {v // v ∈ S})) := by
    simpa only [Fintype.card_option,Fintype.card_coe] using hS.add_odd odd_one
  have hv2 : Even (Fintype.card (Option {v // v ∈ Sᶜ})) := by
    simpa only [Fintype.card_option,Fintype.card_coe] using hc.add_odd odd_one
  apply G.faceSpace_of_eventually_line hx
  filter_upwards [(G.onSide S).faceSpace_eventually_line hx1 h1,
    (G.onSide Sᶜ).faceSpace_eventually_line hx2 h2] with t ht1 ht2
  rw [← G.sideMarginal_line x S u t] at ht1
  rw [← G.sideMarginal_line x Sᶜ u t] at ht2
  have hp1 : G.sideMarginal (x+t • positiveExtension x u) S ∈ (G.onSide S).polytope := by
    rwa [(G.onSide S).polytope_eq_constraints hv1]
  have hp2 : G.sideMarginal (x+t • positiveExtension x u) Sᶜ ∈ (G.onSide Sᶜ).polytope := by
    rwa [(G.onSide Sᶜ).polytope_eq_constraints hv2]
  obtain ⟨p,hp,hpx⟩ := ((G.onSide S).mem_polytope_iff _).mp hp1
  obtain ⟨q,hq,hqx⟩ := ((G.onSide Sᶜ).mem_polytope_iff _).mp hp2
  have hp := (G.mem_polytope_iff _).mpr (G.couple_laws S _ hp hq (congrFun hpx) (congrFun hqx))
  exact G.polytope_subset_constraintPolytope hp

 theorem faceCodimension_le_sides (G : LooplessGraph V E) {x : E → ℝ}
    (heven : Even (Fintype.card V)) (hx : x ∈ G.constraintPolytope)
    (S : Finset V) (hS : Odd S.card) (ht : G.cutMass x S=1) :
    G.faceCodimension x ≤ (G.onSide S).faceCodimension (G.sideMarginal x S) +
      (G.onSide Sᶜ).faceCodimension (G.sideMarginal x Sᶜ) := by
  classical
  exact quotient_finrank_le_pair (G.faceSpace x) ((G.onSide S).faceSpace (G.sideMarginal x S))
    ((G.onSide Sᶜ).faceSpace (G.sideMarginal x Sᶜ))
    (G.sideRestriction x S) (G.sideRestriction x Sᶜ)
    (fun _ => G.faceSpace_of_side_spaces heven hx S hS ht)

/-- Strong face-codimension induction for even orders at least four. -/
theorem faceCodimension_strong_aux (n : ℕ) :
    ∀ {W F : Type*} [Fintype W] [Fintype F] [DecidableEq W] [DecidableEq F]
      (G : LooplessGraph W F), Fintype.card W=n → Even n → 4≤n →
      ∀ x ∈ G.constraintPolytope, G.faceCodimension x ≤ 2*(n-2) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro W F _ _ _ _ G hcard heven hfour x hx
    have heven' : Even (Fintype.card W) := hcard ▸ heven
    by_cases hcut : ∃ S : Finset W, Odd S.card ∧ 3≤S.card ∧ 3≤Sᶜ.card ∧ G.cutMass x S=1
    · obtain ⟨S,hS,hlo,hhi,ht⟩ := hcut
      have hc := odd_compl_of_even heven' hS
      have hlt1 : Fintype.card (Option {v // v ∈ S}) < n := by
        simp only [Fintype.card_option,Fintype.card_coe]
        have hco := Finset.card_compl S
        omega
      have hlt2 : Fintype.card (Option {v // v ∈ Sᶜ}) < n := by
        simp only [Fintype.card_option,Fintype.card_coe]
        have hco := Finset.card_compl S
        have hle := Finset.card_le_univ S
        omega
      have hv1 : Even (Fintype.card (Option {v // v ∈ S})) := by
        simpa only [Fintype.card_option,Fintype.card_coe] using hS.add_odd odd_one
      have hv2 : Even (Fintype.card (Option {v // v ∈ Sᶜ})) := by
        simpa only [Fintype.card_option,Fintype.card_coe] using hc.add_odd odd_one
      have hn1 : 4≤Fintype.card (Option {v // v ∈ S}) := by
        simp only [Fintype.card_option,Fintype.card_coe]; omega
      have hn2 : 4≤Fintype.card (Option {v // v ∈ Sᶜ}) := by
        simp only [Fintype.card_option,Fintype.card_coe]; omega
      have hx1 := G.restriction_mem_constraints hx S hS ht
      have htc : G.cutMass x Sᶜ=1 := by simpa only [cutMass,cut_compl] using ht
      have hx2 := G.restriction_mem_constraints hx Sᶜ hc htc
      have hb1 := ih _ hlt1 (G.onSide S) rfl hv1 hn1 _ hx1
      have hb2 := ih _ hlt2 (G.onSide Sᶜ) rfl hv2 hn2 _ hx2
      have hb := G.faceCodimension_le_sides heven' hx S hS ht
      have hsum : Fintype.card (Option {v // v ∈ S}) + Fintype.card (Option {v // v ∈ Sᶜ})=n+2 := by
        simp only [Fintype.card_option,Fintype.card_coe]
        have hh := Finset.card_compl_add_card S
        omega
      change (G.onSide S).faceCodimension (G.sideMarginal x S) ≤ _ at hb1
      change (G.onSide Sᶜ).faceCodimension (G.sideMarginal x Sᶜ) ≤ _ at hb2
      omega
    · have hb := G.faceCodimension_no_tight heven' hcut
      omega

/-- The precise coarse face-codimension estimate used by the entropy argument. -/
theorem faceCodimension_bound (G : LooplessGraph V E) {x : E → ℝ}
    (heven : Even (Fintype.card V)) (hx : x ∈ G.polytope) :
    G.faceCodimension x ≤ 2*Fintype.card V := by
  by_cases hn : 4≤Fintype.card V
  · have hb := faceCodimension_strong_aux (Fintype.card V) G rfl heven hn x
      (G.polytope_subset_constraintPolytope hx)
    omega
  · have hnt : ¬ ∃ S : Finset V, Odd S.card ∧ 3≤S.card ∧ 3≤Sᶜ.card ∧ G.cutMass x S=1 := by
      rintro ⟨S,_,hlo,hhi,_⟩
      have hh := Finset.card_compl_add_card S
      omega
    have hb := G.faceCodimension_no_tight heven hnt
    omega


omit [Fintype V] [DecidableEq E] in
 theorem degree_add_smul (G : LooplessGraph V E) (x u : E → ℝ) (t : ℝ) (v : V) :
    G.degree (x+t • u) v=G.degree x v+t*G.degree u v := by
  simpa using G.degree_linear x u 1 t v

omit [Fintype V] [DecidableEq E] in
 theorem cutMass_add_smul (G : LooplessGraph V E) (x u : E → ℝ) (t : ℝ) (S : Finset V) :
    G.cutMass (x+t • u) S=G.cutMass x S+t*G.cutMass u S := by
  simpa using G.cutMass_linear x u 1 t S

omit [DecidableEq E] in
/-- Radial extension for this actual matching polytope. This is needed to prove
lower semicontinuity of the maximum entropy without assuming its regularity. -/
theorem constraint_eventually_expand (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x ∈ G.constraintPolytope) {t : ℝ} (ht : 0<t) :
    ∀ᶠ y in 𝓝[G.constraintPolytope] x, x+t⁻¹ • (y-x) ∈ G.constraintPolytope := by
  have hn : ∀ᶠ y in 𝓝[G.constraintPolytope] x, ∀ e, 0≤(x+t⁻¹ • (y-x)) e := by
    apply Filter.eventually_all.mpr
    intro e
    by_cases he : x e=0
    · filter_upwards [eventually_mem_nhdsWithin] with y hy
      simpa [he] using mul_nonneg (inv_nonneg.mpr ht.le) (hy.1 e)
    · have hp : 0<x e := lt_of_le_of_ne (hx.1 e) (Ne.symm he)
      have hc : Continuous (fun y : E → ℝ => (x+t⁻¹ • (y-x)) e) := by fun_prop
      have hh : ∀ᶠ y : E → ℝ in 𝓝 x, 0<(x+t⁻¹ • (y-x)) e :=
        (isOpen_lt continuous_const hc).mem_nhds (by simpa using hp)
      exact (hh.filter_mono nhdsWithin_le_nhds).mono fun y hy => hy.le
  have hodd : ∀ᶠ y in 𝓝[G.constraintPolytope] x,
      ∀ S : Finset V, Odd S.card → 1≤G.cutMass (x+t⁻¹ • (y-x)) S := by
    apply Filter.eventually_all.mpr
    intro S
    by_cases hS : Odd S.card
    · by_cases hs : G.cutMass x S=1
      · filter_upwards [eventually_mem_nhdsWithin] with y hy _
        rw [cutMass_add_smul,cutMass_sub,hs]
        have hh := mul_nonneg (inv_nonneg.mpr ht.le) (sub_nonneg.mpr (hy.2.2 S hS))
        linarith
      · have hp : 1<G.cutMass x S := lt_of_le_of_ne (hx.2.2 S hS) (Ne.symm hs)
        have hc : Continuous (fun y : E → ℝ => G.cutMass (x+t⁻¹ • (y-x)) S) :=
          (G.continuous_cutMass S).comp (by fun_prop)
        have hh : ∀ᶠ y : E → ℝ in 𝓝 x, 1<G.cutMass (x+t⁻¹ • (y-x)) S :=
          (isOpen_lt continuous_const hc).mem_nhds (by simpa using hp)
        exact (hh.filter_mono nhdsWithin_le_nhds).mono fun y hy _ => hy.le
    · exact Filter.Eventually.of_forall fun _ h => (hS h).elim
  filter_upwards [hn,hodd,eventually_mem_nhdsWithin] with y hn hodd hy
  refine ⟨hn,?_,hodd⟩
  intro v
  rw [degree_add_smul,degree_sub,hx.2.1,hy.2.1]
  ring

 theorem polytope_eventually_expand (G : LooplessGraph V E) {x : E → ℝ}
    (heven : Even (Fintype.card V)) (hx : x ∈ G.polytope) {t : ℝ} (ht : 0<t) :
    ∀ᶠ y in 𝓝[G.polytope] x, x+t⁻¹ • (y-x) ∈ G.polytope := by
  rw [G.polytope_eq_constraints heven] at hx ⊢
  exact G.constraint_eventually_expand hx ht

end LooplessGraph

end MatchingEntropy

end

end OAI
