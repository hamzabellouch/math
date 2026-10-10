import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.RationalLattice17
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
noncomputable section
end
 
end

section
 

 

noncomputable section
namespace RationalLattice.PolynomialArrays
open PolynomialArrayInterpolation MalcevCharacters MalcevWeightedCoordinates
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n q : ℕ} (c : RealCoordinates G n) (hsk : SecondKind c)
variable (A : CubeFaces.Filtration G) (w : Fin n → ℕ)
variable (hA : ∀ k (g : G),g∈A.level k ↔ ∀ i : Fin n,w i<k → c.coord g i=0)
variable (hw : ∀ i,0<w i) (hmono : Monotone w)
variable (Γ : Subgroup G) (hΓ : ∀ g : G,g∈Γ ↔ ∀ i,∃ z : ℤ,c.coord g i=z)

include hΓ in
lemma integer_cover : ∃ Λ : Subgroup (group (q:=q) c hsk A w hA),
    ∃ e : RealCoordinates (group (q:=q) c hsk A w hA) (Fintype.card (Index w q)),
    (∀ f,f∈Λ ↔ ∀ i,∃ z : ℤ,e.coord f i=z) ∧
    Λ≤lattice c hsk A w hA Γ ∧ (Λ.subgroupOf (lattice c hsk A w hA Γ)).FiniteIndex ∧
    (∀ f i,e.coord f i=0 ↔ (chart c hsk A w hA hw).coord f i=0) ∧
    (∀ f,IsRational e f ↔ IsRational (chart c hsk A w hA hw) f) := by
  classical
  let d:=chart (q:=q) c hsk A w hA hw
  obtain ⟨D,hD,hgrid⟩:=chart_grid_lattice c hsk A w hA hw (q:=q) Γ hΓ
  obtain ⟨v,hv,hDv,hvgrid⟩:=exists_lattice_weights d D hD
  let Λ:=weightedLattice d v hvgrid
  let e:=scaledCoordinates d v hv
  have hΛ : ∀ f,f∈Λ ↔ ∀ i,∃ z : ℤ,e.coord f i=z:=weightedLattice_iff d v hvgrid hv
  have hle : Λ≤lattice c hsk A w hA Γ := by
    intro f hf
    apply hgrid f
    intro i
    obtain ⟨a,ha⟩:=hf i
    obtain ⟨b,hb⟩:=hDv i
    refine ⟨(b:ℤ)*a,?_⟩
    change d.coord f i=_
    rw [ha,hb]
    push_cast
    ring
  let : T2Space (group (q:=q) c hsk A w hA):=d.coord.symm.t2Space
  let : DiscreteTopology Γ:=integerCoordinates_discrete c Γ hΓ
  let : DiscreteTopology (lattice (q:=q) c hsk A w hA Γ):=lattice_discrete c hsk A w hA Γ
  obtain ⟨C,hC,hrep⟩:=compact_reps_of_integerCoordinates e Λ hΛ
  refine ⟨Λ,e,hΛ,hle,TriangularDenominators.finiteIndex_of_compact_reps Λ
    (lattice c hsk A w hA Γ) hle C hC hrep,?_,scaledCoordinates_rational d v hv⟩
  intro f i
  change d.coord f i/(v i:ℝ)=0 ↔ d.coord f i=0
  have hne : (v i:ℝ)≠0:=by exact_mod_cast (hv i).ne'
  simp only [div_eq_zero_iff,hne,or_false]

include hw hmono hΓ in
lemma second_integer_cover : ∃ Λ : Subgroup (group (q:=q) c hsk A w hA),
    ∃ e : RealCoordinates (group (q:=q) c hsk A w hA) (Fintype.card (Index w q)),
    SecondKind e ∧ (∀ f,f∈Λ ↔ ∀ i,∃ z : ℤ,e.coord f i=z) ∧
    Λ≤lattice c hsk A w hA Γ ∧ (Λ.subgroupOf (lattice c hsk A w hA Γ)).FiniteIndex ∧
    (∀ k f,f∈(filtration c hsk A w hA).level k ↔ ∀ i,orderedWeight (q:=q) w i<k → e.coord f i=0) ∧
    (∀ f,IsRational e f ↔ IsRational (chart c hsk A w hA hw) f) := by
  obtain ⟨Λ,d,hΛ,hle,hindex,hzero,hrat⟩:=integer_cover c hsk A w hA hw Γ hΓ (q:=q)
  refine ⟨Λ,secondCoordinates d,secondCoordinates_secondKind d,expCoordinates_lattice d Λ hΛ,
    hle,hindex,?_,fun f=>(secondCoordinates_rational d f).trans (hrat f)⟩
  intro k f
  obtain ⟨r,hr,he⟩:=exists_weight_cutoff (orderedWeight (q:=q) w) (orderedWeight_monotone w) k
  have hd : ∀ f : group (q:=q) c hsk A w hA,f∈(filtration c hsk A w hA).level k ↔
      ∀ i : Fin (Fintype.card (Index w q)),i.val<r → d.coord f i=0 := by
    intro f
    rw [chart_adapted c hsk A w hA hw hmono]
    simp only [← he,hzero]
  simpa only [← he] using secondCoordinates_adapted d ((filtration c hsk A w hA).level k) r hd f

include hw hmono hΓ in
lemma lattice_level_compact_reps (k : ℕ) :
    CompactGroupProducts.HasCompactReps ((filtration (q:=q) c hsk A w hA).level k)
      (lattice c hsk A w hA Γ) := by
  obtain ⟨Λ,e,_,hΛ,hle,_,hadapt,_⟩:=second_integer_cover c hsk A w hA hw hmono Γ hΓ (q:=q)
  obtain ⟨r,hr,he⟩:=exists_weight_cutoff (orderedWeight (q:=q) w) (orderedWeight_monotone w) k
  have htail : (filtration (q:=q) c hsk A w hA).level k=coordinateTail e r := by
    ext f
    rw [hadapt]
    change (∀ i,orderedWeight w i<k → e.coord f i=0) ↔ ∀ i : Fin (Fintype.card (Index w q)),i.val<r → e.coord f i=0
    simp only [he]
  obtain ⟨C,hC,hCT,hrep⟩:=coordinateTail_compact_reps e Λ hΛ r
  rw [← htail] at hCT hrep
  exact ⟨C,hC,hCT,fun f hf=>by
    obtain ⟨a,ha,haf⟩:=hrep f hf
    exact ⟨a,ha,hle haf⟩⟩

include hw hΓ in
lemma lattice_compactSpace : CompactSpace ((group (q:=q) c hsk A w hA)⧸lattice c hsk A w hA Γ) := by
  obtain ⟨Λ,e,hΛ,hle,_,_,_⟩:=integer_cover c hsk A w hA hw Γ hΓ (q:=q)
  obtain ⟨C,hC,hrep⟩:=compact_reps_of_integerCoordinates e Λ hΛ
  apply CompactGroupProducts.HasCompactReps.quotient_compactSpace
  refine ⟨C,hC,fun _ _=>Subgroup.mem_top _,?_⟩
  intro f _
  obtain ⟨a,ha,haf⟩:=hrep f
  exact ⟨a,ha,hle haf⟩

include hw hΓ in
lemma lattice_quotient_t2 : T2Space ((group (q:=q) c hsk A w hA)⧸lattice c hsk A w hA Γ) := by
  let : T2Space (group (q:=q) c hsk A w hA):=(chart c hsk A w hA hw).coord.symm.t2Space
  let : DiscreteTopology Γ:=integerCoordinates_discrete c Γ hΓ
  let : DiscreteTopology (lattice (q:=q) c hsk A w hA Γ):=lattice_discrete c hsk A w hA Γ
  let : IsClosed (lattice (q:=q) c hsk A w hA Γ : Set (group (q:=q) c hsk A w hA)):=
    (lattice (q:=q) c hsk A w hA Γ).isClosed_of_discreteTopology
  infer_instance

end RationalLattice.PolynomialArrays
end
 
end

section
 

 

noncomputable section
namespace RationalLattice.PolynomialArrays
open PolynomialArrayInterpolation MalcevCharacters WeightedPolynomial
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n q : ℕ} (c : RealCoordinates G n) (hsk : SecondKind c)
variable (A : CubeFaces.Filtration G) (w : Fin n → ℕ)
variable (hA : ∀ k (g : G),g∈A.level k ↔ ∀ i : Fin n,w i<k → c.coord g i=0)
variable (hw : ∀ i,0<w i)

 
def evaluate (u : Fin q → ℝ) : group (q:=q) c hsk A w hA →* G where
  toFun f:=f.val u
  map_one':=rfl
  map_mul' _ _:=rfl
lemma evaluate_continuous (u : Fin q → ℝ) : Continuous (evaluate c hsk A w hA u):=
  (continuous_apply u).comp continuous_subtype_val

lemma readout_polynomial (u : Fin q → ℤ) (i : Fin n) :
    RationalPolynomialMap.IsPolynomial (fun x : Fin (Fintype.card (Index w q)) → ℝ=>
      c.coord (evaluate c hsk A w hA (fun j=>(u j:ℝ))
        ((chart c hsk A w hA hw).coord.symm x)) i) := by
  have hin (a : Index w q) : RationalPolynomialMap.IsPolynomial
      (fun x : Fin (Fintype.card (Index w q)) → ℝ=>x ((SortedFiniteWeights.indexing (weight w)).symm a)):=
    RationalPolynomialMap.coordinate _
  have hl (i : Fin n):=RationalPolynomialMap.comp (toLog_integer_polynomial w u i) hin
  have hh:=RationalPolynomialMap.comp (canonicalExp_polynomial c i) hl
  exact hh

lemma evaluate_rational (u : Fin q → ℤ) (f : group (q:=q) c hsk A w hA)
    (hf : IsRational (chart c hsk A w hA hw) f) :
    IsRational c (evaluate c hsk A w hA (fun j=>(u j:ℝ)) f) :=
  rationalHom_rational c (chart c hsk A w hA hw) (evaluate c hsk A w hA (fun j=>(u j:ℝ)))
    (readout_polynomial c hsk A w hA hw u) hf

lemma shift_coordinates (v : Fin q → ℝ) (f : group (q:=q) c hsk A w hA) (a : Index w q) :
    coefficients c hsk A w hA (shift c hsk A w hA v f) a=
      PolynomialArrayInterpolation.coefficients
        (fun u=>toLog w (coefficients c hsk A w hA f) (u+v) a.1) a.2.val := by
  simp only [toLog_coefficients]
  rfl

lemma shift_polynomial (v : Fin q → ℤ) (i : Fin (Fintype.card (Index w q))) :
    RationalPolynomialMap.IsPolynomial (fun x=>(chart c hsk A w hA hw).coord
      (shift c hsk A w hA (fun j=>(v j:ℝ)) ((chart c hsk A w hA hw).coord.symm x)) i) := by
  let a : Index w q:=SortedFiniteWeights.indexing (weight w) i
  change RationalPolynomialMap.IsPolynomial (fun x=>coefficients c hsk A w hA
    (shift c hsk A w hA (fun j=>(v j:ℝ)) ((chart c hsk A w hA hw).coord.symm x)) a)
  simp only [shift_coordinates]
  apply RationalPolynomialMap.finset_sum
  intro z hz
  apply RationalPolynomialMap.mul (RationalPolynomialMap.const _)
  have hin (a : Index w q) : RationalPolynomialMap.IsPolynomial
      (fun x : Fin (Fintype.card (Index w q)) → ℝ=>x ((SortedFiniteWeights.indexing (weight w)).symm a)):=
    RationalPolynomialMap.coordinate _
  have hh:=RationalPolynomialMap.comp (toLog_integer_polynomial w (fun j=>((z j).val:ℤ)+v j) a.1) hin
  have he (x : Fin (Fintype.card (Index w q)) → ℝ) : coefficients c hsk A w hA
      ((chart c hsk A w hA hw).coord.symm x)=(fun a=>x ((SortedFiniteWeights.indexing (weight w)).symm a)):=
    (coefficientHomeomorph c hsk A w hA).apply_symm_apply _
  simpa only [he,Pi.add_def,Int.cast_add,Int.cast_natCast] using hh

lemma shift_rational (v : Fin q → ℤ) (f : group (q:=q) c hsk A w hA)
    (hf : IsRational (chart c hsk A w hA hw) f) :
    IsRational (chart c hsk A w hA hw) (shift c hsk A w hA (fun j=>(v j:ℝ)) f) :=
  rationalHom_rational (chart c hsk A w hA hw) (chart c hsk A w hA hw)
    (shift c hsk A w hA (fun j=>(v j:ℝ))).toMonoidHom
    (shift_polynomial c hsk A w hA hw v) hf

lemma shift_level (v : Fin q → ℝ) (k : ℕ) (f : group (q:=q) c hsk A w hA) :
    shift c hsk A w hA v f∈(filtration c hsk A w hA).level k ↔
      f∈(filtration c hsk A w hA).level k := by
  constructor
  · intro hf u
    have hh:=hf (u-v)
    change f.val (u-v+v)∈A.level k at hh
    simpa only [sub_add_cancel] using hh
  · intro hf u
    exact hf (u+v)

lemma evaluate_level (u : Fin q → ℝ) (k : ℕ) :
    ((filtration c hsk A w hA).level k).map (evaluate c hsk A w hA u)=A.level k := by
  ext g
  constructor
  · rintro ⟨f,hf,rfl⟩
    exact hf u
  · intro hg
    exact ⟨⟨fun _=>g,constant c w g⟩,fun _=>hg,rfl⟩

variable (Γ : Subgroup G)
 
def readout (u : Fin q → ℤ) : (group (q:=q) c hsk A w hA)⧸lattice c hsk A w hA Γ → G⧸Γ:=
  Quotient.lift (fun f=>QuotientGroup.mk (evaluate c hsk A w hA (fun j=>(u j:ℝ)) f)) (by
    intro f g hfg
    exact QuotientGroup.eq.mpr ((QuotientGroup.leftRel_apply.mp hfg) u))
lemma readout_continuous (u : Fin q → ℤ) : Continuous (readout c hsk A w hA Γ u):=
  (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr
    (QuotientGroup.continuous_mk.comp (evaluate_continuous c hsk A w hA _))

def shifted (v : Fin q → ℤ) : (group (q:=q) c hsk A w hA)⧸lattice c hsk A w hA Γ →
    (group (q:=q) c hsk A w hA)⧸lattice c hsk A w hA Γ:=
  Quotient.map (shift c hsk A w hA (fun j=>(v j:ℝ))) (by
    intro f g hfg
    apply QuotientGroup.leftRel_apply.mpr
    rw [← map_inv,← map_mul]
    exact (shift_lattice c hsk A w hA Γ v _).mpr (QuotientGroup.leftRel_apply.mp hfg))
lemma shifted_continuous (v : Fin q → ℤ) : Continuous (shifted c hsk A w hA Γ v):=
  (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr
    (QuotientGroup.continuous_mk.comp (shift_continuous c hsk A w hA _))

lemma shifted_add (v z : Fin q → ℤ) (x : (group (q:=q) c hsk A w hA)⧸lattice c hsk A w hA Γ) :
    shifted c hsk A w hA Γ (v+z) x=shifted c hsk A w hA Γ v (shifted c hsk A w hA Γ z x) := by
  induction x using Quotient.inductionOn with | h f =>
    apply congrArg QuotientGroup.mk
    apply Subtype.ext
    funext u
    change f.val (u+(fun j=>((v+z) j:ℝ)))=f.val ((u+(fun j=>(v j:ℝ)))+(fun j=>(z j:ℝ)))
    apply congrArg f.val
    funext j
    simp only [Pi.add_apply,Int.cast_add]
    ring
lemma shifted_zero (x : (group (q:=q) c hsk A w hA)⧸lattice c hsk A w hA Γ) :
    shifted c hsk A w hA Γ 0 x=x := by
  induction x using Quotient.inductionOn with | h f =>
    apply congrArg QuotientGroup.mk
    apply Subtype.ext
    funext u
    change f.val (u+(fun _=>((0:ℤ):ℝ)))=f.val u
    apply congrArg f.val
    funext j
    simp only [Pi.add_apply,Int.cast_zero,add_zero]

def shiftedHomeomorph (v : Fin q → ℤ) :
    ((group (q:=q) c hsk A w hA)⧸lattice c hsk A w hA Γ) ≃ₜ
      ((group (q:=q) c hsk A w hA)⧸lattice c hsk A w hA Γ) where
  toFun:=shifted c hsk A w hA Γ v
  invFun:=shifted c hsk A w hA Γ (-v)
  left_inv x:=by rw [← shifted_add,neg_add_cancel,shifted_zero]
  right_inv x:=by rw [← shifted_add,add_neg_cancel,shifted_zero]
  continuous_toFun:=shifted_continuous c hsk A w hA Γ v
  continuous_invFun:=shifted_continuous c hsk A w hA Γ (-v)

lemma readout_shifted (u v : Fin q → ℤ)
    (x : (group (q:=q) c hsk A w hA)⧸lattice c hsk A w hA Γ) :
    readout c hsk A w hA Γ u (shifted c hsk A w hA Γ v x)=readout c hsk A w hA Γ (u+v) x := by
  induction x using Quotient.inductionOn with | h f =>
    change QuotientGroup.mk (f.val ((fun j=>(u j:ℝ))+(fun j=>(v j:ℝ))))=
      QuotientGroup.mk (f.val (fun j=>((u+v) j:ℝ)))
    simp only [Pi.add_def,Int.cast_add]

end RationalLattice.PolynomialArrays

end
end
end

end OAI
