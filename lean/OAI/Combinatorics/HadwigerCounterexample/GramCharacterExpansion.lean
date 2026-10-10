import OAI.Combinatorics.HadwigerCounterexample.CrossPatternCorrelation

namespace OAI

/-! # Gram Character Expansion -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Function Finset
open scoped BigOperators
variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {N : ℕ}

def vectorPhase (x y : Vec I) := wsign (dotProduct x y)

theorem vector_expand (x y : Vec I) :
    ind (x=y)=avg unif (fun z => vectorPhase z x*vectorPhase z y) := by
  classical
  have hh (z : Vec I) : vectorPhase z x * vectorPhase z y = wsign (dotL (x+y) z) := by
    unfold vectorPhase
    rw [← wsign_add]
    change _ = wsign (dotProduct _ _)
    rw [dotProduct_comm (x+y),dotProduct_add]
  have hi : dotL (x+y)=0 ↔ x=y := by
    have he : dotL (x+y)=0 ↔ x+y=0 := by
      constructor
      · intro h
        refine dot_ext_zero fun z => ?_
        rw [dotProduct_comm]; exact LinearMap.congr_fun h z
      intro h; rw [h]; exact LinearMap.ext fun z => zero_dotProduct z
    rw [he,←ZModModule.sub_eq_add,sub_eq_zero]
  simp_rw [hh,wsign_lin]
  rw [hi]

abbrev Rail (I : Type) := Finset (I × I)
variable {E : Rail I}

def ledgerM (E : Rail I) (v : Vec E) : Mat I I :=
  Matrix.of (fun x y => if h:(x,y)∈E then v ⟨(x,y),h⟩ else 0)
def railsM (E : Rail I) (M : Mat I I) : Vec E := fun i => M i.val.1 i.val.2

def traced (x : Rack I N) (E : Rail I) (Z : Vec E) :=
  railsM E (x.1ᵀ*x.2)=Z

def withinRail (M : Mat I I) (E : Rail I) :=
  ∀ i j, (i,j)∉ E→M i j=0

omit [Fintype I] in
theorem inLedger (E : Rail I) (v : Vec E) : railsM E (ledgerM E v)=v := by
  classical
  funext i; rcases i with ⟨⟨i,j⟩,h⟩
  simp [ledgerM,railsM,h]

omit [Fintype I] in
theorem within_recorded (E : Rail I) (v : Vec E) :
    withinRail (ledgerM E v) E := fun _ _ h => dite_eq_right h

theorem rail_charge (x : Rack I N) (E : Rail I) (v : Vec E) :
    vectorPhase v (railsM E (x.1ᵀ*x.2))=phasedBy (ledgerM E v) x := by
  classical
  unfold vectorPhase phasedBy
  rw [layer_form]
  let A := x.1ᵀ*x.2
  let r (i : I × I) := ledgerM E v i.1 i.2 * A i.1 i.2
  change wsign _ = wsign (∑ i:I,∑ j:I,r (i,j))
  rw [←Fintype.sum_prod_type]
  congr 1
  change ∑ i:E,_ = ∑ i:I × I,r i
  calc (∑ i:E,_) = ∑ i:E, r i.val := by
                      refine Finset.sum_congr rfl fun i _ => ?_
                      unfold r
                      rw [show ledgerM E v i.val.1 i.val.2 =v i from congr_fun (inLedger E v) i]
                      rfl
       _ = ∑ i ∈ E,r i := Finset.sum_coe_sort ..
       _ = _ := Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => by
         rcases i with ⟨i,j⟩
         unfold r
         simp only [ledgerM,Matrix.of_apply,dite_eq_right hi,zero_mul])

theorem rail_expand (x : Rack I N) (E : Rail I) (Z : Vec E) :
    ind (traced x E Z) =
      avg unif (fun v : Vec E => phasedBy (ledgerM E v) x*vectorPhase v Z) := by
  unfold traced
  rw [vector_expand]
  simp_rw [rail_charge]

omit [Fintype I] in
theorem ledger_zero (E : Rail I) : ledgerM E 0=0 := by
  classical ext; simp [ledgerM]

theorem phased_match (x : Rack I N) (E : Rail I) (Z v : Vec E) (h : traced x E Z) :
    phasedBy (ledgerM E v) x=vectorPhase v Z := by rw [← rail_charge,h]

def crowded (g : Route I J) : Rail I := Finset.univ.filter (fun x => g x.1=g x.2)

def directions (g : Route I J) (A : GeoM g) : Vec (crowded g) := fun x =>
  A (g x.val.1) ⟨x.val.1,rfl⟩ ⟨x.val.2,(mem_filter.mp x.property).2.symm⟩

omit [Fintype J] [DecidableEq I] in
theorem match_crowd (x : Rack I N) (g : Route I J) (A : GeoM g) :
    traced x (crowded g) (directions g A) ↔ gramPart A x := by
  classical
  rw [part_scores]
  constructor
  · intro h i a b
    obtain ⟨a,ha⟩ := a
    obtain ⟨b,hb⟩ := b
    subst i
    let y : crowded g := ⟨(a,b), mem_filter.mpr ⟨mem_univ _, hb.symm⟩⟩
    exact congr_fun h y
  · intro h
    funext i
    exact h _ ⟨_,rfl⟩ ⟨i.val.2,(mem_filter.mp i.property).2.symm⟩

omit [DecidableEq I] in
theorem rail_count (g : Route I J) :
    ((crowded g).card:ℝ)=netSize g := by
  classical
  let E := crowded g
  let e : (Σ j,Port g j × Port g j) ≃ ↑E :=
    { toFun := fun i => ⟨(i.2.1.val,i.2.2.val),mem_filter.mpr ⟨mem_univ _,i.2.1.property.trans
      i.2.2.property.symm⟩⟩
      invFun := fun i => ⟨g i.val.1,⟨_,rfl⟩,⟨i.val.2,(mem_filter.mp i.property).2.symm⟩⟩
      left_inv := by rintro ⟨j,⟨a,ha⟩,⟨b,hb⟩⟩; subst j; rfl
      right_inv i := by rcases i with ⟨⟨i,j⟩,ha⟩; rfl }
  have ht := Fintype.card_congr e
  rw [Fintype.card_coe,Fintype.card_sigma] at ht
  have hx : (crowded g).card=∑ i : J, (Fintype.card (Port g i)*Fintype.card (Port g i)) := by
    rw [ht.symm]; exact Finset.sum_congr rfl fun i _ => Fintype.card_prod ..
  rw [hx,netSize]
  simp only [Nat.cast_sum,Nat.cast_mul,num]

end HadwigerCounterexample

end

end OAI
