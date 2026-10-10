import OAI.Geometry.UnitDistances.Slots

namespace OAI

namespace PlanarUnitDistances.CommonRareScore
open FiniteLaw FiniteStarCoupling TemplateCoupling CommonTemplate RareRows LevelScores RareScore
open scoped Classical
noncomputable section
variable {P Q H A B I L : Type*} [Fintype P] [Fintype Q] [Fintype H]
  [Fintype A] [Fintype B] [Fintype I] [Fintype L]

theorem balanced (π : Law (P×Q)) (h : P → H) (bit : P → Q → Bool)
    (x : P → A×B) (y : Q → A×B)
    (hμ : ∀p,0<(left π).val p) (hκ : ∀q,0<(right π).val q)
    {ζ η : ℝ} (hζ : 0<ζ) (hk : (Fintype.card I:ℝ)*ζ<1)
    (hI : 0<Fintype.card I) (hη : 0<η) (hη' : η<1/2)
    (ε : ℝ) (good : Prop) (l : A×B) :
    let f := event π (fun pq => bit pq.1 pq.2=true)
    let a := templateLaw (I := I) π h
    let m := event π (fun pq => ¬CrossStructure.Consistent (bit pq.1 pq.2) (x pq.1) (y pq.2))
    let J := event π (fun pq => exceptional (minority f) l (x pq.1) ∧ exceptional (minority f) l (y pq.2))
    (if PlaceScore.common ε f then (avg (templates π a) (fun θ => VP (slice π a θ) bit)+VQ π bit)/80000 else 0)≤
      scoreT ε f π a bit x y good l+scoreQ ε f π bit x y good l+
      (if PlaceScore.common ε f then
        12*(m+((Fintype.card I:ℝ)/ζ)*predictionError π h x y+
          samplingError (Fintype.card I) (η^2)/(1-(Fintype.card I:ℝ)*ζ)+8*η)
       else if good then 8*J+12*m else 2) := by
  dsimp only
  by_cases hc : PlaceScore.common ε (event π (fun pq => bit pq.1 pq.2=true))
  · rw [ite_eq_left hc,ite_eq_left hc,common_T π _ bit x y good l hc,common_Q π bit x y good l hc]
    exact common_score π h bit x y hμ hκ hζ hk hI hη hη'
  · rw [ite_eq_right hc,ite_eq_right hc]
    by_cases hg : good
    · rw [ite_eq_left hg]
      have hp := rare_T π (templateLaw (I := I) π h) bit x y good l hc hg
      have hq := rare_Q π bit x y good l hc hg
      dsimp only at hp hq
      linarith
    · rw [ite_eq_right hg]
      linarith [scoreT_lower ε (event π (fun pq => bit pq.1 pq.2=true)) π
        (templateLaw (I := I) π h) bit x y good l,
        scoreQ_lower ε (event π (fun pq => bit pq.1 pq.2=true)) π bit x y good l]

theorem balanced_average (σ : Law L) (π : Law (P×Q)) (h : P → H)
    (bit : L → P → Q → Bool) (x : L → P → A×B) (y : L → Q → A×B)
    (hμ : ∀p,0<(left π).val p) (hκ : ∀q,0<(right π).val q)
    {ζ η : ℝ} (hζ : 0<ζ) (hk : (Fintype.card I:ℝ)*ζ<1)
    (hI : 0<Fintype.card I) (hη : 0<η) (hη' : η<1/2)
    (ε : ℝ) (good : L → Prop) (l : L → A×B) :
    let f := fun s => event π (fun pq => bit s pq.1 pq.2=true)
    let a := templateLaw (I := I) π h
    let m := fun s => event π (fun pq => ¬CrossStructure.Consistent (bit s pq.1 pq.2) (x s pq.1) (y s pq.2))
    let J := fun s => event π (fun pq => exceptional (minority (f s)) (l s) (x s pq.1) ∧
      exceptional (minority (f s)) (l s) (y s pq.2))
    avg σ (fun s => if PlaceScore.common ε (f s) then
      (avg (templates π a) (fun θ => VP (slice π a θ) (bit s))+VQ π (bit s))/80000 else 0)≤
      avg σ (fun s => scoreT ε (f s) π a (bit s) (x s) (y s) (good s) (l s))+
      avg σ (fun s => scoreQ ε (f s) π (bit s) (x s) (y s) (good s) (l s))+
      avg σ (fun s => if PlaceScore.common ε (f s) then
        12*(m s+((Fintype.card I:ℝ)/ζ)*predictionError π h (x s) (y s)+
          samplingError (Fintype.card I) (η^2)/(1-(Fintype.card I:ℝ)*ζ)+8*η)
       else if good s then 8*J s+12*m s else 2) := by
  have hh := avg_mono σ (fun s => balanced π h (bit s) (x s) (y s) hμ hκ hζ hk hI hη hη' ε (good s) (l s))
  simpa only [avg_add] using hh
end
end PlanarUnitDistances.CommonRareScore

namespace PlanarUnitDistances.RareMass
open FiniteLaw CrossStructure RareScore LevelScores
open scoped Classical
noncomputable section
variable {A B E : Type*} [Fintype E]

def nonsharedCoord {D : Type*} (r : Bool) (x : D×D) : D := if r then x.2 else x.1

lemma coordinate_mismatch {D : Type*} (r b : Bool) (x y : D×D)
    (h : nonsharedCoord r x≠nonsharedCoord r y) : b=r ∨ ¬Consistent b x y := by
  cases r <;> cases b <;> simp_all [nonsharedCoord,Consistent]

lemma minority_mass (μ : Law E) (b : E → Bool) :
    event μ (fun e => b e=minority (event μ (fun e => b e=true)))=
      min (event μ (fun e => b e=true)) (1-event μ (fun e => b e=true)) := by
  let p := event μ (fun e => b e=true)
  have hcomp : event μ (fun e => b e=false)=1-p := by
    change _=1-event μ (fun e => b e=true)
    rw [←event_compl]
    apply avg_congr
    intro e
    cases b e <;> simp
  change event μ (fun e => b e=minority p)=min p (1-p)
  by_cases hp : p<1/2
  · rw [minority,show decide (p<1/2)=true from decide_eq_true hp,min_eq_left (by linarith)]
  · rw [minority,show decide (p<1/2)=false from decide_eq_false hp,hcomp,min_eq_right (by linarith)]

theorem minority_le_exceptions (μ : Law E) (b : E → Bool) (x y : E → A×B) (l : A×B) :
    let p := event μ (fun e => b e=true)
    min p (1-p) ≤ event μ (fun e => exceptional (minority p) l (x e))+
      event μ (fun e => exceptional (minority p) l (y e))+
      event μ (fun e => ¬Consistent (b e) (x e) (y e)) := by
  dsimp only
  rw [←minority_mass μ b]
  have h := event_mono μ (fun e (hb : b e=minority (event μ (fun e => b e=true))) =>
    show (exceptional (minority (event μ (fun e => b e=true))) l (x e) ∨
      exceptional (minority (event μ (fun e => b e=true))) l (y e)) ∨
      ¬Consistent (b e) (x e) (y e) from by
      by_cases hc : Consistent (b e) (x e) (y e)
      · exact Or.inl (minority_exception hc hb)
      · exact Or.inr hc)
  exact h.trans ((event_union_le μ _ _).trans (add_le_add (event_union_le μ _ _) le_rfl))

lemma mismatch_le_minority_error {D : Type*} (μ : Law E) (b : E → Bool) (x y : E → D×D) :
    let p := event μ (fun e => b e=true)
    event μ (fun e => nonsharedCoord (minority p) (x e)≠nonsharedCoord (minority p) (y e)) ≤
      min p (1-p)+event μ (fun e => ¬Consistent (b e) (x e) (y e)) := by
  dsimp only
  rw [←minority_mass μ b]
  exact (event_mono μ (fun e h => coordinate_mismatch _ _ _ _ h)).trans (event_union_le μ _ _)
end
end PlanarUnitDistances.RareMass

namespace PlanarUnitDistances.RareLabels
open FiniteLaw FiniteStarCoupling LevelScores RareScore RareMass
open scoped Classical
noncomputable section
variable {P Q A : Type*} [Fintype P] [Fintype Q] [Fintype A]

def minorityMass (π : Law (P×Q)) (bit : P → Q → Bool) : ℝ :=
  min (event π (fun pq => bit pq.1 pq.2=true)) (1-event π (fun pq => bit pq.1 pq.2=true))
def error (π : Law (P×Q)) (bit : P → Q → Bool) (x : P → A×A) (y : Q → A×A) : ℝ :=
  event π (fun pq => ¬CrossStructure.Consistent (bit pq.1 pq.2) (x pq.1) (y pq.2))
omit [Fintype A] in
lemma exception_diag (r : Bool) (l : A) (x : A×A) :
    exceptional r (l,l) x ↔ nonsharedCoord r x≠l := by cases r <;> simp [exceptional,nonsharedCoord]

theorem dominant {γ η : ℝ} (hγ : 0<γ) (hη : 0<η) :
    ∃s₀ ξ₀ C : ℝ,0<s₀ ∧ 0<ξ₀ ∧ 0<C ∧
    ∀ (P Q A : Type) [Fintype P] [Fintype Q] [Fintype A],
    ∀(π : Law (P×Q)) (U : Law P) (W : Law Q),
    (∀p,γ*U.val p≤(left π).val p) → (∀q,γ*W.val q≤(right π).val q) →
    ∀ξ : ℝ,0≤ξ → ξ≤ξ₀ →
    (∀F : Finset P,∀G : Finset Q,event π (fun pq => pq.1∈F ∧ pq.2∈G)≤
      Real.sqrt (event U (fun p => p∈F)*event W (fun q => q∈G))*
        ((event U (fun p => p∈F)*event W (fun q => q∈G))^η+ξ)) →
    ∀(bit : P → Q → Bool) (x : P → A×A) (y : Q → A×A),
    minorityMass π bit+error π bit x y≤ s₀ →
    ∃l : A×A,event (left π) (fun p => exceptional (minority (event π (fun pq => bit pq.1 pq.2=true))) l (x p))+
      event (right π) (fun q => exceptional (minority (event π (fun pq => bit pq.1 pq.2=true))) l (y q))≤
        C*(minorityMass π bit+error π bit x y) := by
  obtain ⟨s₀,ξ₀,C,hs,hξ,hC,hm⟩ := LawExpansion.matching hγ hη
  refine ⟨s₀,ξ₀,C,hs,hξ,hC,?_⟩
  intro P Q A _ _ _ π U W hl hr ξ hξ0 hξb hexp bit x y hsmall
  let r := minority (event π (fun pq => bit pq.1 pq.2=true))
  have hd := mismatch_le_minority_error π (fun pq => bit pq.1 pq.2) (fun pq => x pq.1) (fun pq => y pq.2)
  change event π (fun pq => nonsharedCoord r (x pq.1)≠nonsharedCoord r (y pq.2))≤
    minorityMass π bit+error π bit x y at hd
  obtain ⟨l,hl⟩ := hm P Q A π U W (fun p => nonsharedCoord r (x p)) (fun q => nonsharedCoord r (y q))
    hl hr ξ hξ0 hξb hexp (hd.trans hsmall)
  refine ⟨(l,l),?_⟩
  simp only [exception_diag]
  exact hl.trans (mul_le_mul_of_nonneg_left hd hC.le)

omit [Fintype A] in
lemma minority_le (π : Law (P×Q)) (bit : P → Q → Bool) (x : P → A×A) (y : Q → A×A) (l : A×A) :
    minorityMass π bit≤
    event (left π) (fun p => exceptional (minority (event π (fun pq => bit pq.1 pq.2=true))) l (x p))+
    event (right π) (fun q => exceptional (minority (event π (fun pq => bit pq.1 pq.2=true))) l (y q))+
    error π bit x y := by
  simpa only [left,right,LawExpansion.push_event,minorityMass,error] using
    minority_le_exceptions π (fun pq => bit pq.1 pq.2) (fun pq => x pq.1) (fun pq => y pq.2) l

variable [Nonempty A]

def label (C : ℝ) (π : Law (P×Q)) (bit : P → Q → Bool) (x : P → A×A) (y : Q → A×A) : A×A :=
  if h : ∃l : A×A,event (left π) (fun p => exceptional (minority (event π (fun pq => bit pq.1 pq.2=true))) l (x p))+
    event (right π) (fun q => exceptional (minority (event π (fun pq => bit pq.1 pq.2=true))) l (y q))≤
      C*(minorityMass π bit+error π bit x y) then Classical.choose h else Classical.choice inferInstance

lemma label_spec (C : ℝ) (π : Law (P×Q)) (bit : P → Q → Bool) (x : P → A×A) (y : Q → A×A)
    (h : ∃l : A×A,event (left π) (fun p => exceptional (minority (event π (fun pq => bit pq.1 pq.2=true))) l (x p))+
    event (right π) (fun q => exceptional (minority (event π (fun pq => bit pq.1 pq.2=true))) l (y q))≤
      C*(minorityMass π bit+error π bit x y)) :
    event (left π) (fun p => exceptional (minority (event π (fun pq => bit pq.1 pq.2=true))) (label C π bit x y) (x p))+
    event (right π) (fun q => exceptional (minority (event π (fun pq => bit pq.1 pq.2=true))) (label C π bit x y) (y q))≤
      C*(minorityMass π bit+error π bit x y) := by
  rw [label,dite_eq_left h]
  exact Classical.choose_spec h
end
end PlanarUnitDistances.RareLabels

namespace PlanarUnitDistances.LawRare
open Finset FiniteLaw LawExpansion FiniteStarCoupling
open scoped Classical
noncomputable section
variable {P Q : Type*} [Fintype P] [Fintype Q]

lemma event_domination (μ ν : Law P) {γ : ℝ} (h : ∀p,γ*μ.val p≤ν.val p) (F : P → Prop) :
    γ*event μ F≤event ν F := by
  unfold event avg
  rw [mul_sum]
  apply sum_le_sum
  intro p _
  by_cases hp : F p <;> simp [hp,h p]

theorem small_rect (π : Law (P×Q)) (U : Law P) (W : Law Q) {γ η ξ a : ℝ}
    (hγ : 0<γ) (hη : 0≤η) (hξ : 0≤ξ)
    (hl : ∀p,γ*U.val p≤(left π).val p) (hr : ∀q,γ*W.val q≤(right π).val q)
    (hexp : ∀F : Finset P,∀G : Finset Q,event π (fun pq => pq.1∈F ∧ pq.2∈G)≤
      Real.sqrt (event U (fun p => p∈F)*event W (fun q => q∈G))*
        ((event U (fun p => p∈F)*event W (fun q => q∈G))^η+ξ))
    (F : Finset P) (G : Finset Q) (hF : event (left π) (fun p => p∈F)≤a) :
    event π (fun pq => pq.1∈F ∧ pq.2∈G)≤
      (((a/γ)^η+ξ)/γ)*Real.sqrt (event (left π) (fun p => p∈F)*event (right π) (fun q => q∈G)) := by
  let u := event U (fun p => p∈F)
  let v := event W (fun q => q∈G)
  let h := event (left π) (fun p => p∈F)
  let k := event (right π) (fun q => q∈G)
  have hu : 0≤u := event_nonneg _ _
  have hv : 0≤v := event_nonneg _ _
  have hh : 0≤h := event_nonneg _ _
  have hk : 0≤k := event_nonneg _ _
  have hul : γ*u≤h := event_domination U (left π) hl _
  have hvr : γ*v≤k := event_domination W (right π) hr _
  have hp := mul_le_mul hul hvr (mul_nonneg hγ.le hv) hh
  have hs : γ*Real.sqrt (u*v)≤Real.sqrt (h*k) := by
    apply (sq_le_sq₀ (mul_nonneg hγ.le (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)).mp
    rw [mul_pow,Real.sq_sqrt (mul_nonneg hu hv),Real.sq_sqrt (mul_nonneg hh hk)]
    nlinarith
  have huv : u*v≤a/γ := by
    have ha : u≤a/γ := (le_div_iff₀ hγ).mpr (by linarith)
    exact (mul_le_of_le_one_right hu (event_le_one W _)).trans ha
  have he := Real.rpow_le_rpow (mul_nonneg hu hv) huv hη
  have han : 0≤(a/γ)^η+ξ := add_nonneg (Real.rpow_nonneg (div_nonneg (hh.trans hF) hγ.le) _) hξ
  have hs' : Real.sqrt (u*v)≤Real.sqrt (h*k)/γ := (le_div_iff₀ hγ).mpr (by nlinarith)
  calc
    _ ≤ Real.sqrt (u*v)*((u*v)^η+ξ) := hexp F G
    _ ≤ Real.sqrt (u*v)*((a/γ)^η+ξ) := mul_le_mul_of_nonneg_left (by linarith) (Real.sqrt_nonneg _)
    _ ≤ (Real.sqrt (h*k)/γ)*((a/γ)^η+ξ) := mul_le_mul_of_nonneg_right hs' han
    _ = _ := by ring

lemma sqrt_le_half_sum {h k : ℝ} (hh : 0≤h) (hk : 0≤k) : Real.sqrt (h*k)≤(h+k)/2 := by
  have hs := Real.sq_sqrt (mul_nonneg hh hk)
  have hn := Real.sqrt_nonneg (h*k)
  nlinarith [sq_nonneg (h-k)]

theorem edge_rare (π : Law (P×Q)) (F : Finset P) (G : Finset Q) {θ : ℝ} (hθ : 0≤θ)
    (h : event π (fun pq => pq.1∈F ∧ pq.2∈G)≤
      θ*Real.sqrt (event (left π) (fun p => p∈F)*event (right π) (fun q => q∈G))) :
    event π (fun pq => pq.1∈F ∧ pq.2∈G)≤
      θ/2*(event (left π) (fun p => p∈F)+event (right π) (fun q => q∈G)) := by
  have h' := mul_le_mul_of_nonneg_left (sqrt_le_half_sum (event_nonneg (left π) (fun p => p∈F)) (event_nonneg (right π) (fun q => q∈G))) hθ
  calc
    _ ≤ θ*Real.sqrt _ := h
    _ ≤ θ*((event (left π) (fun p => p∈F)+event (right π) (fun q => q∈G))/2) := h'
    _ = _ := by ring
end
end PlanarUnitDistances.LawRare

namespace PlanarUnitDistances.LawWedges
open Finset FiniteLaw FiniteStarCoupling
open scoped Classical
noncomputable section
variable {P Q : Type*} [Fintype P] [Fintype Q]

lemma conditional_eq (π : Law (P×Q)) (F : Finset P) {q : Q} (hq : 0<(right π).val q) :
    ExpansionConsequences.conditional (fun p q => π.val (p,q)) F q=event (col π q) (fun p => p∈F) := by
  simp only [ExpansionConsequences.conditional,LawExpansion.right_val]
  rw [←LawExpansion.mass_event]
  simp only [ExpansionConsequences.mass,col_val π hq,sum_div]

lemma wedgeMass_eq (π : Law (P×Q)) (F : Finset P) :
    ExpansionConsequences.wedgeMass (fun p q => π.val (p,q)) F=
      avg (right π) (fun q => (event (col π q) (fun p => p∈F))^2) := by
  unfold ExpansionConsequences.wedgeMass avg
  apply sum_congr rfl
  intro q _
  rw [LawExpansion.right_val]
  by_cases hq : 0<(right π).val q
  · rw [conditional_eq π F hq]
  · have hz := le_antisymm (le_of_not_gt hq) ((right π).nonneg q)
    simp only [hz,zero_mul]

theorem rare (π : Law (P×Q)) (F : Finset P) {θ d : ℝ} (hθ : 0≤θ) (hd : 0<d)
    (hexp : ∀G : Finset Q,event π (fun pq => pq.1∈F ∧ pq.2∈G)≤
      θ*Real.sqrt (event (left π) (fun p => p∈F)*event (right π) (fun q => q∈G))) :
    avg (right π) (fun q => (event (col π q) (fun p => p∈F))^2)≤
      (d+θ/Real.sqrt d)*event (left π) (fun p => p∈F) := by
  have h := ExpansionConsequences.wedge_rare (fun p q => π.val (p,q)) (fun p q => π.nonneg (p,q)) F hθ hd
  have hl : ExpansionConsequences.left (fun p q => π.val (p,q))=(left π).val := funext (LawExpansion.left_val π)
  have hr : ExpansionConsequences.right (fun p q => π.val (p,q))=(right π).val := funext (LawExpansion.right_val π)
  simp only [LawExpansion.rect_event,hl,hr,LawExpansion.mass_event] at h
  simpa only [wedgeMass_eq π F] using h hexp

lemma pair_event_sq (μ : Law P) (F : P → Prop) :
    event (pair μ μ) (fun pp => F pp.1 ∧ F pp.2)=(event μ F)^2 := by
  have h := pair_prod μ μ (fun p => if F p then 1 else 0) (fun p => if F p then 1 else 0)
  have he : event (pair μ μ) (fun pp => F pp.1 ∧ F pp.2)=
      avg (pair μ μ) (fun pp => (if F pp.1 then 1 else 0)*(if F pp.2 then 1 else 0)) := by
    apply avg_congr
    intro pp
    split_ifs <;> simp_all
  rw [he,h]
  simp only [event,pow_two]
end
end PlanarUnitDistances.LawWedges

namespace PlanarUnitDistances.RareMoments
open Finset FiniteLaw FiniteStarCoupling RareLabels LevelScores RareScore
open scoped Classical
noncomputable section
variable {P Q A : Type} [Fintype P] [Fintype Q] [Fintype A]

def hp (π : Law (P×Q)) (bit : P → Q → Bool) (x : P → A×A) (l : A×A) : ℝ :=
  event (left π) (fun p => exceptional (minority (event π (fun pq => bit pq.1 pq.2=true))) l (x p))
def hq (π : Law (P×Q)) (bit : P → Q → Bool) (y : Q → A×A) (l : A×A) : ℝ :=
  event (right π) (fun q => exceptional (minority (event π (fun pq => bit pq.1 pq.2=true))) l (y q))
def joint (π : Law (P×Q)) (bit : P → Q → Bool) (x : P → A×A) (y : Q → A×A) (l : A×A) : ℝ :=
  event π (fun pq => exceptional (minority (event π (fun rs => bit rs.1 rs.2=true))) l (x pq.1) ∧
    exceptional (minority (event π (fun rs => bit rs.1 rs.2=true))) l (y pq.2))
def wedge (π : Law (P×Q)) (bit : P → Q → Bool) (x : P → A×A) (l : A×A) : ℝ :=
  avg (right π) (fun q => event (pair (col π q) (col π q)) (fun pp =>
    exceptional (minority (event π (fun rs => bit rs.1 rs.2=true))) l (x pp.1) ∧
    exceptional (minority (event π (fun rs => bit rs.1 rs.2=true))) l (x pp.2)))

omit [Fintype A] in
theorem joint_wedge (π : Law (P×Q)) (U : Law P) (W : Law Q) {γ η ξ a d : ℝ}
    (hγ : 0<γ) (hη : 0≤η) (hξ : 0≤ξ) (ha : 0≤a) (hd : 0<d)
    (hl : ∀p,γ*U.val p≤(left π).val p) (hr : ∀q,γ*W.val q≤(right π).val q)
    (hexp : ∀F : Finset P,∀G : Finset Q,event π (fun pq => pq.1∈F ∧ pq.2∈G)≤
      Real.sqrt (event U (fun p => p∈F)*event W (fun q => q∈G))*
        ((event U (fun p => p∈F)*event W (fun q => q∈G))^η+ξ))
    (bit : P → Q → Bool) (x : P → A×A) (y : Q → A×A) (l : A×A)
    (hx : hp π bit x l≤a) :
    joint π bit x y l≤(((a/γ)^η+ξ)/γ)/2*(hp π bit x l+hq π bit y l) ∧
    wedge π bit x l≤(d+(((a/γ)^η+ξ)/γ)/Real.sqrt d)*hp π bit x l := by
  let F := univ.filter (fun p => exceptional (minority (event π (fun rs => bit rs.1 rs.2=true))) l (x p))
  let G := univ.filter (fun q => exceptional (minority (event π (fun rs => bit rs.1 rs.2=true))) l (y q))
  have hF : event (left π) (fun p => p∈F)≤a := by simpa only [F,mem_filter,mem_univ,true_and,hp] using hx
  have ht : 0≤((a/γ)^η+ξ)/γ := div_nonneg
    (add_nonneg (Real.rpow_nonneg (div_nonneg ha hγ.le) _) hξ) hγ.le
  have he := LawRare.edge_rare π F G ht (LawRare.small_rect π U W hγ hη hξ hl hr hexp F G hF)
  have hw := LawWedges.rare π F ht hd (fun G => LawRare.small_rect π U W hγ hη hξ hl hr hexp F G hF)
  simp only [F,G,mem_filter,mem_univ,true_and] at he hw
  constructor
  · exact he
  · calc
      _ = avg (right π) (fun q => (event (col π q) (fun p =>
          exceptional (minority (event π (fun rs => bit rs.1 rs.2=true))) l (x p)))^2) := by
        apply avg_congr
        intro q
        exact LawWedges.pair_event_sq (col π q) (fun p =>
          exceptional (minority (event π (fun rs => bit rs.1 rs.2=true))) l (x p))
      _ ≤ _ := hw

theorem uniform {γ η : ℝ} (hγ : 0<γ) (hη : 0<η) :
    ∃s₀ ξ₀ C : ℝ,0<s₀ ∧ 0<ξ₀ ∧ 0<C ∧
    ∀(P Q A : Type) [Fintype P] [Fintype Q] [Fintype A],
    ∀(π : Law (P×Q)) (U : Law P) (W : Law Q),
    (∀p,γ*U.val p≤(left π).val p) → (∀q,γ*W.val q≤(right π).val q) →
    ∀ξ : ℝ,0≤ξ → ξ≤ξ₀ →
    (∀F : Finset P,∀G : Finset Q,event π (fun pq => pq.1∈F ∧ pq.2∈G)≤
      Real.sqrt (event U (fun p => p∈F)*event W (fun q => q∈G))*
        ((event U (fun p => p∈F)*event W (fun q => q∈G))^η+ξ)) →
    ∀ ε τ d : ℝ,0≤ε → 0≤τ → 0<d → ε+τ≤ s₀ →
    ∀(bit : P → Q → Bool) (x : P → A×A) (y : Q → A×A),
    minorityMass π bit≤ε → error π bit x y≤τ →
    ∃l : A×A,
      hp π bit x l+hq π bit y l≤C*(minorityMass π bit+error π bit x y) ∧
      minorityMass π bit≤hp π bit x l+hq π bit y l+error π bit x y ∧
      joint π bit x y l≤((((C*(ε+τ))/γ)^η+ξ)/γ)/2*(hp π bit x l+hq π bit y l) ∧
      wedge π bit x l≤(d+((((C*(ε+τ))/γ)^η+ξ)/γ)/Real.sqrt d)*hp π bit x l := by
  obtain ⟨s₀,ξ₀,C,hs,hξ,hC,hm⟩ := RareLabels.dominant hγ hη
  refine ⟨s₀,ξ₀,C,hs,hξ,hC,?_⟩
  intro P Q A _ _ _ π U W hl hr ξ hξ0 hξb hexp ε τ d hε hτ hd hsum bit x y hf he
  obtain ⟨l,hdom⟩ := hm P Q A π U W hl hr ξ hξ0 hξb hexp bit x y (by linarith)
  have hb : hp π bit x l≤C*(ε+τ) := by
    have hq0 : 0≤hq π bit y l := event_nonneg _ _
    have hh : C*(minorityMass π bit+error π bit x y)≤C*(ε+τ) :=
      mul_le_mul_of_nonneg_left (by linarith) hC.le
    change hp π bit x l+hq π bit y l≤_ at hdom
    linarith
  obtain ⟨hj,hw⟩ := joint_wedge π U W hγ hη.le hξ0 (mul_nonneg hC.le (add_nonneg hε hτ)) hd
    hl hr hexp bit x y l hb
  exact ⟨l,hdom,RareLabels.minority_le π bit x y l,hj,hw⟩
end
end PlanarUnitDistances.RareMoments

namespace PlanarUnitDistances.FiniteLaw
open Finset
open scoped Classical
noncomputable section
variable {X : Type*} [Fintype X]
lemma event_markov (μ : Law X) (f : X → ℝ) (hf : ∀x,0≤f x) {ε : ℝ} (hε : 0<ε) :
    event μ (fun x => ε<f x)≤avg μ f/ε := by
  apply (le_div_iff₀ hε).mpr
  rw [mul_comm]; unfold event; rw [←avg_smul]
  apply avg_mono
  intro x
  split_ifs with h
  · simpa using h.le
  · simpa using hf x
end
end PlanarUnitDistances.FiniteLaw

namespace PlanarUnitDistances.CommonTemplate
open Finset FiniteLaw FiniteStarCoupling StrictCross CrossSampling CrossStructure FiniteMarginalScore
open scoped Classical
noncomputable section
variable {P Q H A B : Type*} [Fintype P] [Fintype Q] [Fintype H] [Fintype A] [Fintype B]
omit [Fintype H] in

theorem marginal_score (π : Law (P×Q)) (h : P → H) (bit : P → Q → Bool)
    (x : P → A×B) (y : Q → A×B) {ε : ℝ} (hε : 0<ε) :
    VP π bit/80000≤DP π bit y+avg (left π) (fun p => tau (posteriorState π h x (h p)))+
      20*(event π (fun pq => ¬Consistent (bit pq.1 pq.2) (x pq.1) (y pq.2))+
        predictionError π h x y/ε+ε) := by
  let good : P → Q → Prop := fun p q => Consistent (bit p q) (x p) (y q) ∧
    1-ε≤crossMass (posteriorState π h x (h p)) (y q)
  have hs := avg_mono (left π) (fun p => second_slice (row π p) (bit p) y
    (posteriorState π h x (h p)) (x p) (good p) hε.le
    (fun _ hg => hg.1) (fun _ hg => hg.2))
  simp only [avg_sub,div_eq_mul_inv,avg_add,avg_smul,avg_const] at hs
  have hv : avg (left π) (fun p => StarScore.variation (row π p) (bit p)*80000⁻¹)=VP π bit*80000⁻¹ := by
    simp [VP,avg,Finset.sum_mul,mul_assoc]
  rw [hv,row_event] at hs
  have hb : event π (fun pq => ¬good pq.1 pq.2)≤
      event π (fun pq => ¬Consistent (bit pq.1 pq.2) (x pq.1) (y pq.2))+
      predictionError π h x y/ε := by
    refine (event_mono π ?_).trans ((event_union_le π _ _).trans (add_le_add_right
      (event_markov π (fun pq => 1-crossMass (posteriorState π h x (h pq.1)) (y pq.2))
        (fun pq => sub_nonneg.mpr (event_le_one _ _)) hε) _))
    intro pq hg
    by_cases hc : Consistent (bit pq.1 pq.2) (x pq.1) (y pq.2)
    · right
      have hn : ¬1-ε≤crossMass (posteriorState π h x (h pq.1)) (y pq.2) := fun hp => hg ⟨hc,hp⟩
      linarith
    · exact Or.inl hc
  change _≤DP π bit y+_ at hs
  linarith
end
end PlanarUnitDistances.CommonTemplate

namespace PlanarUnitDistances.FiniteStarCoupling
open Finset FiniteLaw
open scoped Classical
noncomputable section
variable {P Q : Type*} [Fintype P] [Fintype Q]
lemma joint_le_left (π : Law (P×Q)) (p : P) (q : Q) : π.val (p,q)≤(left π).val p := by
  rw [left_val]
  exact single_le_sum (fun r _ => π.nonneg (p,r)) (mem_univ q)
lemma conditional_collision (π : Law (P×Q)) {M : ℝ} (hM : ∀p,(left π).val p≤M) :
    avg (right π) (fun q => ∑p,(col π q).val p^2)≤(Fintype.card Q:ℝ)*M := by
  unfold avg
  calc
    _ = ∑q,∑p,π.val (p,q)*(col π q).val p := by
      apply sum_congr rfl; intro q _
      rw [mul_sum]
      apply sum_congr rfl; intro p _
      rw [pow_two,←mul_assoc,col_weight]
    _ ≤ ∑q,∑p,M*(col π q).val p := by
      apply sum_le_sum; intro q _
      apply sum_le_sum; intro p _
      exact mul_le_mul_of_nonneg_right ((joint_le_left π p q).trans (hM p)) ((col π q).nonneg p)
    _ = _ := by simp [←mul_sum,(col π _).total]
end
end PlanarUnitDistances.FiniteStarCoupling

namespace PlanarUnitDistances.LevelBookkeeping
open Finset FiniteLaw FiniteStarCoupling RareLabels RareMoments RareScore
open scoped Classical
noncomputable section
variable {D P Q A : Type} [Fintype D] [Fintype P] [Fintype Q] [Fintype A]

def goodRare (ε τ : ℝ) (π : Law (P×Q)) (b : P → Q → Bool) (x : P → A×A) (y : Q → A×A) : Prop :=
  ¬PlaceScore.common ε (event π (fun pq => b pq.1 pq.2=true)) ∧ error π b x y ≤ τ

def damaged (ε τ : ℝ) (π : Law (P×Q)) (b : P → Q → Bool) (x : P → A×A) (y : Q → A×A) : Prop :=
  ¬PlaceScore.common ε (event π (fun pq => b pq.1 pq.2=true)) ∧ τ < error π b x y

omit [Fintype D] [Fintype A] in
lemma minority_nonneg (π : Law (P×Q)) (b : P → Q → Bool) : 0 ≤ minorityMass π b :=
  le_min (event_nonneg _ _) (sub_nonneg.mpr (event_le_one _ _))
omit [Fintype D] [Fintype A] in
lemma minority_le_half (π : Law (P×Q)) (b : P → Q → Bool) : minorityMass π b ≤ 1/2 := by
  unfold minorityMass
  have := min_le_left (event π (fun pq => b pq.1 pq.2=true)) (1-event π (fun pq => b pq.1 pq.2=true))
  have := min_le_right (event π (fun pq => b pq.1 pq.2=true)) (1-event π (fun pq => b pq.1 pq.2=true))
  linarith
omit [Fintype D] [Fintype A] in
lemma not_common (π : Law (P×Q)) (b : P → Q → Bool) {ε : ℝ}
    (h : ¬PlaceScore.common ε (event π (fun pq => b pq.1 pq.2=true))) : minorityMass π b < ε := by
  unfold PlaceScore.common at h
  unfold minorityMass
  rcases not_and_or.mp h with h | h
  · exact (min_le_left _ _).trans_lt (lt_of_not_ge h)
  · exact (min_le_right _ _).trans_lt (by linarith)

theorem select {γ η : ℝ} (hγ : 0<γ) (hη : 0<η) :
    ∃s₀ ξ₀ C : ℝ,0<s₀ ∧ 0<ξ₀ ∧ 0<C ∧
    ∀(D P Q A : Type) [Fintype D] [Fintype P] [Fintype Q] [Fintype A] [Nonempty A],
    ∀(π : Law (P×Q)) (U : Law P) (W : Law Q),
    (∀p,γ*U.val p ≤ (left π).val p) → (∀q,γ*W.val q ≤ (right π).val q) →
    ∀ξ : ℝ,0 ≤ ξ → ξ ≤ ξ₀ →
    (∀F : Finset P,∀G : Finset Q,event π (fun pq => pq.1∈F ∧ pq.2∈G) ≤
      Real.sqrt (event U (fun p => p∈F)*event W (fun q => q∈G))*
        ((event U (fun p => p∈F)*event W (fun q => q∈G))^η+ξ)) →
    ∀ ε τ d : ℝ,0 ≤ ε → 0 ≤ τ → 0<d → ε+τ ≤ s₀ →
    ∀(b : D → P → Q → Bool) (x : D → P → A×A) (y : D → Q → A×A),
    ∃l : D → A×A,∀s, goodRare ε τ π (b s) (x s) (y s) →
      hp π (b s) (x s) (l s)+hq π (b s) (y s) (l s) ≤ C*(minorityMass π (b s)+error π (b s) (x s) (y s)) ∧
      minorityMass π (b s) ≤ hp π (b s) (x s) (l s)+hq π (b s) (y s) (l s)+error π (b s) (x s) (y s) ∧
      joint π (b s) (x s) (y s) (l s) ≤ ((((C*(ε+τ))/γ)^η+ξ)/γ)/2*(hp π (b s) (x s) (l s)+hq π (b s) (y s) (l s)) ∧
      wedge π (b s) (x s) (l s) ≤ (d+((((C*(ε+τ))/γ)^η+ξ)/γ)/Real.sqrt d)*hp π (b s) (x s) (l s) := by
  obtain ⟨s₀,ξ₀,C,hs,hξ,hC,hh⟩ := RareMoments.uniform hγ hη
  refine ⟨s₀,ξ₀,C,hs,hξ,hC,?_⟩
  intro D P Q A _ _ _ _ _ π U W hl hr ξ hξ0 hξb hexp ε τ d hε hτ hd hsum b x y
  have he : ∀s,∃l : A×A, goodRare ε τ π (b s) (x s) (y s) →
      hp π (b s) (x s) l+hq π (b s) (y s) l ≤ C*(minorityMass π (b s)+error π (b s) (x s) (y s)) ∧
      minorityMass π (b s) ≤ hp π (b s) (x s) l+hq π (b s) (y s) l+error π (b s) (x s) (y s) ∧
      joint π (b s) (x s) (y s) l ≤ ((((C*(ε+τ))/γ)^η+ξ)/γ)/2*(hp π (b s) (x s) l+hq π (b s) (y s) l) ∧
      wedge π (b s) (x s) l ≤ (d+((((C*(ε+τ))/γ)^η+ξ)/γ)/Real.sqrt d)*hp π (b s) (x s) l := by
    intro s
    by_cases hg : goodRare ε τ π (b s) (x s) (y s)
    · obtain ⟨l,hl⟩ := hh P Q A π U W hl hr ξ hξ0 hξb hexp ε τ d hε hτ hd hsum
        (b s) (x s) (y s) (not_common π (b s) hg.1).le hg.2
      exact ⟨l,fun _ => hl⟩
    · exact ⟨Classical.choice inferInstance,fun h => False.elim (hg h)⟩
  choose l hl using he
  exact ⟨l,hl⟩

omit [Fintype A] in

theorem widths (σ : Law D) (π : Law (P×Q)) (b : D → P → Q → Bool)
    (x : D → P → A×A) (y : D → Q → A×A) {ε τ : ℝ} (hε : 0<ε) (hτ : 0<τ) :
    event σ (fun s => PlaceScore.common ε (event π (fun pq => b s pq.1 pq.2=true))) ≤
      avg σ (fun s => minorityMass π (b s))/ε ∧
    event σ (fun s => damaged ε τ π (b s) (x s) (y s)) ≤
      avg σ (fun s => error π (b s) (x s) (y s))/τ := by
  constructor
  · apply (le_div_iff₀ hε).mpr
    rw [mul_comm]
    unfold event
    rw [←avg_smul]
    apply avg_mono
    intro s
    split_ifs with hs
    · rw [mul_one]
      have he : ε ≤ event π (fun pq => b s pq.1 pq.2=true) ∧
        event π (fun pq => b s pq.1 pq.2=true) ≤ 1-ε := hs
      exact le_min he.1 (by linarith [he.2])
    · simpa using minority_nonneg π (b s)
  · refine (event_mono σ (fun s hs => hs.2)).trans ?_
    exact event_markov σ (fun s => error π (b s) (x s) (y s)) (fun _ => event_nonneg _ _) hτ

omit [Fintype A] in

theorem moments (σ : Law D) (π : Law (P×Q)) (b : D → P → Q → Bool)
    (x : D → P → A×A) (y : D → Q → A×A) (l : D → A×A) {ε τ C θ ψ : ℝ}
    (hC : 0 ≤ C)
    (h : ∀s,goodRare ε τ π (b s) (x s) (y s) →
      hp π (b s) (x s) (l s)+hq π (b s) (y s) (l s) ≤ C*(minorityMass π (b s)+error π (b s) (x s) (y s)) ∧
      joint π (b s) (x s) (y s) (l s) ≤ θ*(hp π (b s) (x s) (l s)+hq π (b s) (y s) (l s)) ∧
      wedge π (b s) (x s) (l s) ≤ ψ*hp π (b s) (x s) (l s)) :
    let R := fun s => goodRare ε τ π (b s) (x s) (y s)
    let HP := avg σ (fun s => if R s then hp π (b s) (x s) (l s) else 0)
    let HQ := avg σ (fun s => if R s then hq π (b s) (y s) (l s) else 0)
    HP+HQ ≤ C*(avg σ (fun s => minorityMass π (b s))+avg σ (fun s => error π (b s) (x s) (y s))) ∧
    avg σ (fun s => if R s then joint π (b s) (x s) (y s) (l s) else 0) ≤ θ*(HP+HQ) ∧
    avg σ (fun s => if R s then wedge π (b s) (x s) (l s) else 0) ≤ ψ*HP := by
  dsimp only
  constructor
  · rw [←avg_add,←avg_add,←avg_smul]
    apply avg_mono
    intro s
    split_ifs with hs
    · exact (h s hs).1
    · simpa only [zero_add,error] using mul_nonneg hC (add_nonneg (minority_nonneg π (b s))
        (event_nonneg π (fun pq => ¬CrossStructure.Consistent (b s pq.1 pq.2) (x s pq.1) (y s pq.2))))
  constructor
  · rw [←avg_add,←avg_smul]
    apply avg_mono
    intro s
    split_ifs with hs
    · exact (h s hs).2.1
    · simp
  · rw [←avg_smul]
    apply avg_mono
    intro s
    split_ifs with hs
    · exact (h s hs).2.2
    · simp
end
end PlanarUnitDistances.LevelBookkeeping

namespace PlanarUnitDistances.FiniteLaw
open scoped Classical
noncomputable section
variable {D : Type*} [Fintype D]
lemma avg_neg (σ : Law D) (f : D → ℝ) : avg σ (fun s => -f s) = -avg σ f := by
  simp only [avg,mul_neg,Finset.sum_neg_distrib]
def cut (σ : Law D) (c : D → Prop) (f : D → ℝ) : ℝ := avg σ (fun s => if c s then f s else 0)
lemma cut_add (σ : Law D) (c : D → Prop) (f g : D → ℝ) :
    cut σ c (fun s => f s+g s)=cut σ c f+cut σ c g := by
  unfold cut; rw [←avg_add]; apply avg_congr; intro s; split_ifs <;> simp
lemma cut_smul (σ : Law D) (c : D → Prop) (a : ℝ) (f : D → ℝ) :
    cut σ c (fun s => a*f s)=a*cut σ c f := by
  unfold cut; rw [←avg_smul]; apply avg_congr; intro s; split_ifs <;> simp
lemma cut_const (σ : Law D) (c : D → Prop) (a : ℝ) : cut σ c (fun _ => a)=a*event σ c := by
  unfold cut event
  rw [←avg_smul]; apply avg_congr; intro s; split_ifs <;> simp
lemma cut_nonneg (σ : Law D) (c : D → Prop) (f : D → ℝ) (hf : ∀s,0 ≤ f s) : 0 ≤ cut σ c f :=
  avg_nonneg σ (fun s => by split_ifs <;> first | exact hf s | exact le_rfl)
lemma cut_le_avg (σ : Law D) (c : D → Prop) (f : D → ℝ) (hf : ∀s,0 ≤ f s) : cut σ c f ≤ avg σ f :=
  avg_mono σ (fun s => by split_ifs <;> first | exact le_rfl | exact hf s)
lemma cut_mono (σ : Law D) (c : D → Prop) (f g : D → ℝ) (hf : ∀s,c s → f s ≤ g s) :
    cut σ c f ≤ cut σ c g := avg_mono σ (fun s => by split_ifs with h; exact hf s h; rfl)
end
end PlanarUnitDistances.FiniteLaw

end OAI
