import OAI.InformationTheory.PhotonNumber.BeamForms

namespace OAI

noncomputable section

open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open ContinuousLinearMap
open scoped ENNReal

namespace PhysicalGenerator
open EntropyPhotonNumber QuantumTrace Annihilation BeamLadder
open scoped BigOperators ComplexConjugate
variable {n : ℕ} {I : Type*}

def lowerCoefficient (j : Fin n) (k : NumberIndex n) : ℂ := Real.sqrt ((k j:ℝ)+1)
def raiseCoefficient (j : Fin n) (k : NumberIndex n) : ℂ :=
  if k j=0 then 0 else Real.sqrt (k j:ℝ)
def modeCoefficient (j : Fin n) (u : Bool) (k : NumberIndex n) : ℂ :=
  (k j:ℂ)+(if u then 1 else 0)

def lowerFamily (j : Fin n) (x : I → Fock n) := fun i => sandwich 0 3 (by omega) j (x i)
def raiseFamily (j : Fin n) (x : I → Fock n) := fun i => creationSandwich 0 3 (by omega) j (x i)
def modeFamily (j : Fin n) (u : Bool) (x : I → Fock n) := fun i => inverseWeight 2 (modeBound j u (x i))
def baseFamily (x : I → Fock n) := fun i => inverseWeight 3 (x i)

def dissipator (j : Fin n) (u : Bool) (x : I → Fock n) : Fock n →L[ℂ] Fock n :=
  CrossEnsemble.operator (if u then raiseFamily j x else lowerFamily j x)
      (if u then raiseFamily j x else lowerFamily j x)-
    (2:ℂ)⁻¹ • (CrossEnsemble.operator (modeFamily j u x) (baseFamily x)+
      CrossEnsemble.operator (baseFamily x) (modeFamily j u x))
def generator (r : ℝ) (x : I → Fock n) : Fock n →L[ℂ] Fock n :=
  ∑ j, (((r+1:ℝ):ℂ) • dissipator j false x+(r:ℂ) • dissipator j true x)

theorem pairing_hasSum {J : Type*} (b : HilbertBasis J ℂ (Fock n))
    (r : ℝ) (x : I → Fock n) (hx : Summable (fun i => ‖x i‖^2))
    (Z : Fock n →L[ℂ] Fock n) :
    HasSum (fun k => inner ℂ (b k) (Z (generator r x (b k)))) (singleGeneratorPairing r x Z) := by
  have hl (j : Fin n) := CrossEnsemble.applied_summable hx (sandwich 0 3 (by omega) j)
  have hr (j : Fin n) := CrossEnsemble.applied_summable hx (creationSandwich 0 3 (by omega) j)
  have hm (j : Fin n) (u : Bool) := CrossEnsemble.applied_summable hx (inverseWeight 2 ∘L modeBound j u)
  have hi := CrossEnsemble.applied_summable hx (inverseWeight 3)
  have hl' (j : Fin n) := (CrossEnsemble.pairing_trace b (hl j) (hl j) Z).sub
    (((CrossEnsemble.pairing_trace b (hm j false) hi Z).add
      (CrossEnsemble.pairing_trace b hi (hm j false) Z)).mul_left (2:ℂ)⁻¹)
  have hr' (j : Fin n) := (CrossEnsemble.pairing_trace b (hr j) (hr j) Z).sub
    (((CrossEnsemble.pairing_trace b (hm j true) hi Z).add
      (CrossEnsemble.pairing_trace b hi (hm j true) Z)).mul_left (2:ℂ)⁻¹)
  have hh := hasSum_sum fun j (_hj : j ∈ (Finset.univ : Finset (Fin n))) =>
    ((hl' j).mul_left ((r+1:ℝ):ℂ)).add ((hr' j).mul_left (r:ℂ))
  convert! hh using 1
  ext k
  simp only [generator,dissipator,
    Bool.false_eq_true,ite_false,ite_true,sum_apply,add_apply,sub_apply,smul_apply,
    map_sum,map_add,map_sub,map_smul,inner_sum,inner_sub_right,inner_add_right,inner_smul_right]
  rfl

theorem dissipator_entry (x : I → Fock n) (hx : Summable (fun i => ‖x i‖^2))
    (j : Fin n) (u : Bool) (k l : NumberIndex n) :
    entry (dissipator j u x) k l =
      (if u then raiseCoefficient j k*conj (raiseCoefficient j l)*
        entry (CrossEnsemble.operator (baseFamily x) (baseFamily x)) (down j k) (down j l)
      else lowerCoefficient j k*conj (lowerCoefficient j l)*
        entry (CrossEnsemble.operator (baseFamily x) (baseFamily x)) (up j k) (up j l))-
      (2:ℂ)⁻¹*((modeCoefficient j u k+conj (modeCoefficient j u l))*
        entry (CrossEnsemble.operator (baseFamily x) (baseFamily x)) k l) := by
  have hi : Summable (fun i => ‖baseFamily x i‖^2) := CrossEnsemble.applied_summable hx (inverseWeight 3)
  have hm : Summable (fun i => ‖modeFamily j u x i‖^2) :=
    CrossEnsemble.applied_summable hx (inverseWeight 2 ∘L modeBound j u)
  have hml := CrossEnsemble.entry_transform (modeFamily j u x) (baseFamily x) (baseFamily x) (baseFamily x)
    hm hi hi hi k l k l (modeCoefficient j u k) 1 (by
      intro i
      simp only [modeFamily,baseFamily,single_number_third_apply,modeCoefficient,map_one,mul_one]
      ring)
  have hmr := CrossEnsemble.entry_transform (baseFamily x) (modeFamily j u x) (baseFamily x) (baseFamily x)
    hi hm hi hi k l k l 1 (modeCoefficient j u l) (by
      intro i
      simp only [modeFamily,baseFamily,single_number_third_apply,modeCoefficient,one_mul,map_mul]
      ring)
  have hg : entry (CrossEnsemble.operator (if u then raiseFamily j x else lowerFamily j x)
      (if u then raiseFamily j x else lowerFamily j x)) k l =
      (if u then raiseCoefficient j k*conj (raiseCoefficient j l)*
        entry (CrossEnsemble.operator (baseFamily x) (baseFamily x)) (down j k) (down j l)
      else lowerCoefficient j k*conj (lowerCoefficient j l)*
        entry (CrossEnsemble.operator (baseFamily x) (baseFamily x)) (up j k) (up j l)) := by
    cases u
    · simp only [Bool.false_eq_true,ite_false]
      apply CrossEnsemble.entry_transform _ _ _ _
        (CrossEnsemble.applied_summable hx (sandwich 0 3 (by omega) j))
        (CrossEnsemble.applied_summable hx (sandwich 0 3 (by omega) j)) hi hi
      intro i
      simp only [baseFamily,single_lower_third_apply,lowerCoefficient,map_mul]
      ring
    · simp only [ite_true]
      apply CrossEnsemble.entry_transform _ _ _ _
        (CrossEnsemble.applied_summable hx (creationSandwich 0 3 (by omega) j))
        (CrossEnsemble.applied_summable hx (creationSandwich 0 3 (by omega) j)) hi hi
      intro i
      simp only [baseFamily,single_raise_third_apply,raiseCoefficient,map_mul]
      ring
  have hout : entry (dissipator j u x) k l=entry (CrossEnsemble.operator
      (if u then raiseFamily j x else lowerFamily j x) (if u then raiseFamily j x else lowerFamily j x)) k l-
    (2:ℂ)⁻¹*(entry (CrossEnsemble.operator (modeFamily j u x) (baseFamily x)) k l+
      entry (CrossEnsemble.operator (baseFamily x) (modeFamily j u x)) k l) := by
    simp only [entry,dissipator,sub_apply,smul_apply,add_apply,inner_sub_right,inner_smul_right,inner_add_right]
  rw [hout,hg,hml,hmr]
  simp only [map_one,mul_one,one_mul]
  ring

theorem lowerCoefficient_self (j : Fin n) (k : NumberIndex n) :
    lowerCoefficient j k*conj (lowerCoefficient j k)=(k j:ℂ)+1 := by
  simp only [lowerCoefficient,Complex.conj_ofReal,← Complex.ofReal_mul,
    Real.mul_self_sqrt (by positivity : 0≤(k j:ℝ)+1)]
  push_cast
  rfl

theorem raiseCoefficient_self (j : Fin n) (k : NumberIndex n) :
    raiseCoefficient j k*conj (raiseCoefficient j k)=(k j:ℂ) := by
  by_cases hk : k j=0
  · simp [raiseCoefficient,hk]
  · simp only [raiseCoefficient,ite_eq_right hk,Complex.conj_ofReal,← Complex.ofReal_mul,
      Real.mul_self_sqrt (Nat.cast_nonneg (k j)), Complex.ofReal_natCast]

theorem modeCoefficient_conj (j : Fin n) (u : Bool) (k : NumberIndex n) :
    conj (modeCoefficient j u k)=modeCoefficient j u k := by
  cases u <;> simp [modeCoefficient]

theorem generator_zero_of_geometric_diagonal (r : ℝ) (p : NumberIndex n → ℝ)
    (hb : ∀ j k, ((r+1:ℝ):ℂ)*(p (up j k):ℂ)=(r:ℂ)*(p k:ℂ))
    (x : I → Fock n) (hx : Summable (fun i => ‖x i‖^2))
    (he : ∀ k l, entry (CrossEnsemble.operator (baseFamily x) (baseFamily x)) k l=
      if k=l then (p k:ℂ) else 0) : generator r x=0 := by
  have hj (j : Fin n) : ((r+1:ℝ):ℂ) • dissipator j false x+(r:ℂ) • dissipator j true x=0 := by
    apply entry_ext
    intro k l
    have hs : entry (((r+1:ℝ):ℂ) • dissipator j false x+(r:ℂ) • dissipator j true x) k l=
      ((r+1:ℝ):ℂ)*entry (dissipator j false x) k l+(r:ℂ)*entry (dissipator j true x) k l := by
      simp only [entry,add_apply,smul_apply,inner_add_right,inner_smul_right]
    rw [hs,dissipator_entry x hx j false,dissipator_entry x hx j true]
    simp only [Bool.false_eq_true,ite_false,ite_true,he,modeCoefficient_conj]
    by_cases hkl : k=l
    · subst l
      simp only [ite_true,lowerCoefficient_self,raiseCoefficient_self,modeCoefficient,
        Bool.false_eq_true,ite_false,add_zero,ite_true,entry,zero_apply,inner_zero_right]
      have hb1 := hb j k
      by_cases hk : k j=0
      · simp only [hk,Nat.cast_zero,zero_add,one_mul,zero_mul,add_zero,mul_zero,sub_zero]
        linear_combination hb1
      · have hb2 := hb j (down j k)
        rw [up_down j k (Nat.pos_of_ne_zero hk)] at hb2
        linear_combination ((k j:ℂ)+1)*hb1-(k j:ℂ)*hb2
    · have hup : up j k≠up j l := fun h => hkl (up_injective j h)
      have hr : raiseCoefficient j k*conj (raiseCoefficient j l)*
          (if down j k=down j l then (p (down j k):ℂ) else 0)=0 := by
        by_cases hk : k j=0
        · simp [raiseCoefficient,hk]
        by_cases hl : l j=0
        · simp [raiseCoefficient,hl]
        have hd : down j k≠down j l := by
          intro hh
          have hh' := congrArg (up j) hh
          rw [up_down j k (Nat.pos_of_ne_zero hk),up_down j l (Nat.pos_of_ne_zero hl)] at hh'
          exact hkl hh'
        rw [ite_eq_right hd,mul_zero]
      rw [ite_eq_right hkl,ite_eq_right hup,hr]
      simp only [mul_zero,sub_zero,add_zero,entry,zero_apply,inner_zero_right]
  simp only [generator,hj,Finset.sum_const_zero]

theorem weighted_pairing_zero_of_geometric_diagonal (r : ℝ) (p : NumberIndex n → ℝ)
    (hb : ∀ j k, ((r+1:ℝ):ℂ)*(p (up j k):ℂ)=(r:ℂ)*(p k:ℂ))
    (x : I → Fock n) (hx : Summable (fun i => ‖x i‖^2))
    (he : ∀ k l, entry (CrossEnsemble.operator (baseFamily x) (baseFamily x)) k l=
      if k=l then (p k:ℂ) else 0) (B : Fock n →L[ℂ] Fock n) :
    WeightedGenerator.pairing r x B=0 := by
  let bas : HilbertBasis (NumberIndex n) ℂ (Fock n) :=
    HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)
  have hg := generator_zero_of_geometric_diagonal r p hb x hx he
  have hzero : HasSum (fun _ : NumberIndex n => (0:ℂ)) 0 := hasSum_zero
  have hphys (Z : Fock n →L[ℂ] Fock n) : singleGeneratorPairing r x Z=0 := by
    have hh := pairing_hasSum bas r x hx Z
    have hz : HasSum (fun _ : NumberIndex n => (0:ℂ)) (singleGeneratorPairing r x Z) := by
      simpa only [hg,zero_apply,map_zero,inner_zero_right] using hh
    exact hz.unique hzero
  apply weighted_trace_ext bas (WeightedGenerator.generator r x) 0
    (WeightedGenerator.pairing r x) (fun _ => 0)
    (fun Z => WeightedGenerator.pairing_hasSum bas r x hx Z)
    (fun Z => by simpa only [zero_apply,map_zero,inner_zero_right] using hzero)
    (fun Z => by rw [weighted_pairing_physical,hphys]) B
end PhysicalGenerator

namespace QuantumTrace
theorem thermalWeight_number (n : ℕ) (r : ℝ) (k : Fin n → ℕ) :
    thermalWeight n r k=(r+1)⁻¹^n*(r/(r+1))^(∑ j,k j) := by
  simp [thermalWeight,Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]

theorem thermalWeight_up {n : ℕ} (r : ℝ) (j : Fin n) (k : Fin n → ℕ) :
    thermalWeight n r (Annihilation.up j k)=r/(r+1)*thermalWeight n r k := by
  have hs : (∑ i,Annihilation.up j k i)=(∑ i,k i)+1 := by
    simp [Annihilation.up,Finset.sum_add_distrib]
  rw [thermalWeight_number,thermalWeight_number,hs,pow_succ]
  ring

theorem thermalWeight_balance {n : ℕ} (r : ℝ) (hr : 0<r) (j : Fin n) (k : Fin n → ℕ) :
    ((r+1:ℝ):ℂ)*(thermalWeight n r (Annihilation.up j k):ℂ)=
      (r:ℂ)*(thermalWeight n r k:ℂ) := by
  have h : (r+1)*thermalWeight n r (Annihilation.up j k)=r*thermalWeight n r k := by
    rw [thermalWeight_up]
    have hr1 : r+1≠0 := by positivity
    field_simp
  exact_mod_cast h
end QuantumTrace

namespace PhysicalGenerator

section
open EntropyPhotonNumber QuantumTrace
variable {n : ℕ} {I : Type*}

theorem weighted_thermal_pairing_zero (r : ℝ) (hr : 0<r)
    (x : I → Fock n) (hx : Summable (fun i => ‖x i‖^2))
    (he : ∀ k l, entry (CrossEnsemble.operator (baseFamily x) (baseFamily x)) k l=
      if k=l then (thermalWeight n r k:ℂ) else 0) (B : Fock n →L[ℂ] Fock n) :
    WeightedGenerator.pairing r x B=0 :=
  weighted_pairing_zero_of_geometric_diagonal r (thermalWeight n r)
    (thermalWeight_balance r hr) x hx he B
end

open EntropyPhotonNumber QuantumTrace Annihilation BeamLadder
open scoped BigOperators ComplexConjugate
variable {n : ℕ} {I J K : Type*}

theorem dissipator_affine (c d : ℂ) (x : I → Fock n) (y : J → Fock n) (z : K → Fock n)
    (hx : Summable (fun i => ‖x i‖^2)) (hy : Summable (fun j => ‖y j‖^2))
    (hz : Summable (fun k => ‖z k‖^2))
    (he : CrossEnsemble.operator (baseFamily z) (baseFamily z)=
      c • CrossEnsemble.operator (baseFamily x) (baseFamily x)+
      d • CrossEnsemble.operator (baseFamily y) (baseFamily y))
    (j : Fin n) (u : Bool) : dissipator j u z=c • dissipator j u x+d • dissipator j u y := by
  have he' (k l : NumberIndex n) :
      entry (CrossEnsemble.operator (baseFamily z) (baseFamily z)) k l=
      c*entry (CrossEnsemble.operator (baseFamily x) (baseFamily x)) k l+
      d*entry (CrossEnsemble.operator (baseFamily y) (baseFamily y)) k l := by
    rw [he]
    simp only [entry,add_apply,smul_apply,inner_add_right,inner_smul_right]
  apply entry_ext
  intro k l
  have hs : entry (c • dissipator j u x+d • dissipator j u y) k l=
      c*entry (dissipator j u x) k l+d*entry (dissipator j u y) k l := by
    simp only [entry,add_apply,smul_apply,inner_add_right,inner_smul_right]
  rw [hs,dissipator_entry z hz,dissipator_entry x hx,dissipator_entry y hy]
  simp only [he']
  cases u <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> ring

theorem generator_affine (r : ℝ) (c d : ℂ) (x : I → Fock n) (y : J → Fock n) (z : K → Fock n)
    (hx : Summable (fun i => ‖x i‖^2)) (hy : Summable (fun j => ‖y j‖^2))
    (hz : Summable (fun k => ‖z k‖^2))
    (he : CrossEnsemble.operator (baseFamily z) (baseFamily z)=
      c • CrossEnsemble.operator (baseFamily x) (baseFamily x)+
      d • CrossEnsemble.operator (baseFamily y) (baseFamily y)) :
    generator r z=c • generator r x+d • generator r y := by
  unfold generator
  simp only [dissipator_affine c d x y z hx hy hz he,smul_add,Finset.smul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  module

theorem pairing_affine (r : ℝ) (c d : ℂ) (x : I → Fock n) (y : J → Fock n) (z : K → Fock n)
    (hx : Summable (fun i => ‖x i‖^2)) (hy : Summable (fun j => ‖y j‖^2))
    (hz : Summable (fun k => ‖z k‖^2))
    (he : CrossEnsemble.operator (baseFamily z) (baseFamily z)=
      c • CrossEnsemble.operator (baseFamily x) (baseFamily x)+
      d • CrossEnsemble.operator (baseFamily y) (baseFamily y)) (Z : Fock n →L[ℂ] Fock n) :
    singleGeneratorPairing r z Z=c*singleGeneratorPairing r x Z+d*singleGeneratorPairing r y Z := by
  let bas : HilbertBasis (NumberIndex n) ℂ (Fock n) := HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)
  apply (pairing_hasSum bas r z hz Z).unique
  rw [generator_affine r c d x y z hx hy hz he]
  simpa only [add_apply,smul_apply,map_add,map_smul,inner_add_right,inner_smul_right] using
    ((pairing_hasSum bas r x hx Z).mul_left c).add ((pairing_hasSum bas r y hy Z).mul_left d)

theorem weighted_pairing_affine (r : ℝ) (c d : ℂ) (x : I → Fock n) (y : J → Fock n) (z : K → Fock n)
    (hx : Summable (fun i => ‖x i‖^2)) (hy : Summable (fun j => ‖y j‖^2))
    (hz : Summable (fun k => ‖z k‖^2))
    (he : CrossEnsemble.operator (baseFamily z) (baseFamily z)=
      c • CrossEnsemble.operator (baseFamily x) (baseFamily x)+
      d • CrossEnsemble.operator (baseFamily y) (baseFamily y)) (B : Fock n →L[ℂ] Fock n) :
    WeightedGenerator.pairing r z B=c*WeightedGenerator.pairing r x B+d*WeightedGenerator.pairing r y B := by
  let bas : HilbertBasis (NumberIndex n) ℂ (Fock n) := HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)
  apply weighted_trace_ext bas (WeightedGenerator.generator r z)
    (c • WeightedGenerator.generator r x+d • WeightedGenerator.generator r y)
    (WeightedGenerator.pairing r z) (fun Z => c*WeightedGenerator.pairing r x Z+d*WeightedGenerator.pairing r y Z)
  · exact fun Z => WeightedGenerator.pairing_hasSum bas r z hz Z
  · intro Z
    simpa only [add_apply,smul_apply,map_add,map_smul,inner_add_right,inner_smul_right] using
      ((WeightedGenerator.pairing_hasSum bas r x hx Z).mul_left c).add
        ((WeightedGenerator.pairing_hasSum bas r y hy Z).mul_left d)
  · intro Z
    simp only [weighted_pairing_physical]
    exact pairing_affine r c d x y z hx hy hz he Z
end PhysicalGenerator

namespace EntropyPhotonNumber
open QuantumTrace Annihilation BeamLadder

structure WeightedColumns {n : ℕ} (ρ : State n) where
  Index : Type
  vector : Index → Fock n
  summable : Summable (fun i => ‖vector i‖^2)
  normalized : HasSum (fun i => ‖inverseWeight 3 (vector i)‖^2) 1
  density : TraceEnsemble.operator (fun i => inverseWeight 3 (vector i))=ρ.op

namespace WeightedColumns
variable {n : ℕ} {ρ : State n} (X : WeightedColumns ρ)

theorem base_density :
    CrossEnsemble.operator (PhysicalGenerator.baseFamily X.vector) (PhysicalGenerator.baseFamily X.vector)=ρ.op :=
  X.density

def slice (η : ℝ) (hη : η ∈ Set.Icc 0 1) (B : Fock n →L[ℂ] Fock n) : Fock n →L[ℂ] Fock n :=
  weightedConditional η hη (fun i => inverseWeight 1 (X.vector i)) B

def sliceRight (η : ℝ) (hη : η ∈ Set.Icc 0 1) (B : Fock n →L[ℂ] Fock n) : Fock n →L[ℂ] Fock n :=
  weightedConditionalRight η hη (fun i => inverseWeight 1 (X.vector i)) B

theorem thermal_pairing_zero (r : ℝ) (hr : 0<r)
    (he : ∀ k l, entry ρ.op k l=if k=l then (thermalWeight n r k:ℂ) else 0)
    (B : Fock n →L[ℂ] Fock n) : WeightedGenerator.pairing r X.vector B=0 := by
  apply PhysicalGenerator.weighted_thermal_pairing_zero r hr X.vector X.summable
  intro k l
  rw [X.base_density,he]
end WeightedColumns

theorem weighted_replaced_threeport_generator
    {n : ℕ} (η θ κ a b d : ℝ) (hη : η ∈ Set.Icc 0 1) (hθ : θ ∈ Set.Icc 0 1)
    (ρ σ τD m γ ω ρ0 : State n)
    (h1 : IsBeamSplitterOutput η ρ σ m) (h2 : IsBeamSplitterOutput θ m τD γ)
    (X : WeightedColumns ρ) (Y : WeightedColumns σ) (D : WeightedColumns τD)
    (M : WeightedColumns m) (G : WeightedColumns γ) (O : WeightedColumns ω) (Z : WeightedColumns ρ0)
    (hd : 0<d) (hr0 : 0<θ*(η*a+(1-η)*b)+(1-θ)*d)
    (hD : ∀ k l, entry τD.op k l=if k=l then (thermalWeight n d k:ℂ) else 0)
    (hO : ∀ k l, entry ω.op k l=
      if k=l then (thermalWeight n (θ*(η*a+(1-η)*b)+(1-θ)*d) k:ℂ) else 0)
    (hZ : ρ0.op=((1-κ:ℝ):ℂ) • γ.op+(κ:ℂ) • ω.op)
    (B : Fock n →L[ℂ] Fock n) :
    WeightedGenerator.pairing (θ*(η*a+(1-η)*b)+(1-θ)*d) Z.vector B=
      ((1-κ:ℝ):ℂ)*(WeightedGenerator.pairing a X.vector (Y.slice η hη (D.slice θ hθ B))+
        WeightedGenerator.pairing b Y.vector (X.sliceRight η hη (D.slice θ hθ B))) := by
  have he := PhysicalGenerator.weighted_pairing_affine
    (θ*(η*a+(1-η)*b)+(1-θ)*d) ((1-κ:ℝ):ℂ) (κ:ℂ) G.vector O.vector Z.vector
    G.summable O.summable Z.summable (by rw [Z.base_density,G.base_density,O.base_density,hZ]) B
  rw [he,O.thermal_pairing_zero _ hr0 hO,mul_zero,add_zero]
  have hh2 := weighted_product_generator θ (η*a+(1-η)*b) d hθ m τD γ h2
    M.vector D.vector G.vector M.summable D.summable G.summable
    M.normalized D.normalized M.density D.density G.density B
  have hh1 := weighted_product_generator η a b hη ρ σ m h1
    X.vector Y.vector M.vector X.summable Y.summable M.summable
    X.normalized Y.normalized X.density Y.density M.density (D.slice θ hθ B)
  change WeightedGenerator.pairing _ G.vector B=
    WeightedGenerator.pairing _ M.vector (D.slice θ hθ B)+
      WeightedGenerator.pairing d D.vector (M.sliceRight θ hθ B) at hh2
  rw [D.thermal_pairing_zero d hd hD,add_zero,hh1] at hh2
  rw [hh2]
  rfl
end EntropyPhotonNumber

namespace PhysicalGenerator
open EntropyPhotonNumber QuantumTrace Annihilation BeamLadder
open scoped BigOperators ComplexConjugate
variable {n : ℕ} {I J K : Type*}

def weakOperator (r : ℝ) (j : Fin n) (x : I → Fock n) : Fock n →L[ℂ] Fock n :=
  (r+1:ℂ) • CrossEnsemble.operator (baseFamily x) (lowerFamily j x)-
    (r:ℂ) • CrossEnsemble.operator (raiseFamily j x) (baseFamily x)

theorem weak_pairing_hasSum {L : Type*} (b : HilbertBasis L ℂ (Fock n))
    (r : ℝ) (j : Fin n) (x : I → Fock n) (hx : Summable (fun i => ‖x i‖^2))
    (Z : Fock n →L[ℂ] Fock n) :
    HasSum (fun k => inner ℂ (b k) (Z (weakOperator r j x (b k)))) (singleWeak r j x Z) := by
  have hi := CrossEnsemble.applied_summable hx (inverseWeight 3)
  have hl := CrossEnsemble.applied_summable hx (sandwich 0 3 (by omega) j)
  have hr := CrossEnsemble.applied_summable hx (creationSandwich 0 3 (by omega) j)
  have hh := ((CrossEnsemble.pairing_trace b hi hl Z).mul_left (r+1:ℂ)).sub
    ((CrossEnsemble.pairing_trace b hr hi Z).mul_left (r:ℂ))
  unfold weakOperator
  simp only [smul_apply,sub_apply,map_sub,map_smul,inner_sub_right,inner_smul_right]
  exact hh

theorem weakOperator_entry (r : ℝ) (j : Fin n) (x : I → Fock n)
    (hx : Summable (fun i => ‖x i‖^2)) (k l : NumberIndex n) :
    entry (weakOperator r j x) k l=
      (r+1:ℂ)*conj (lowerCoefficient j l)*entry (CrossEnsemble.operator (baseFamily x) (baseFamily x)) k (up j l)-
      (r:ℂ)*raiseCoefficient j k*entry (CrossEnsemble.operator (baseFamily x) (baseFamily x)) (down j k) l := by
  have hi := CrossEnsemble.applied_summable hx (inverseWeight 3)
  have hl := CrossEnsemble.applied_summable hx (sandwich 0 3 (by omega) j)
  have hr := CrossEnsemble.applied_summable hx (creationSandwich 0 3 (by omega) j)
  have el := CrossEnsemble.entry_transform (baseFamily x) (lowerFamily j x) (baseFamily x) (baseFamily x)
    hi hl hi hi k l k (up j l) 1 (lowerCoefficient j l) (by
      intro i
      simp only [baseFamily,lowerFamily,single_lower_third_apply,lowerCoefficient,map_mul,one_mul]
      ring)
  have er := CrossEnsemble.entry_transform (raiseFamily j x) (baseFamily x) (baseFamily x) (baseFamily x)
    hr hi hi hi k l (down j k) l (raiseCoefficient j k) 1 (by
      intro i
      simp only [baseFamily,raiseFamily,single_raise_third_apply,raiseCoefficient,map_one,mul_one]
      ring)
  have ee : entry (weakOperator r j x) k l=
      (r+1:ℂ)*entry (CrossEnsemble.operator (baseFamily x) (lowerFamily j x)) k l-
      (r:ℂ)*entry (CrossEnsemble.operator (raiseFamily j x) (baseFamily x)) k l := by
    simp only [entry,weakOperator,sub_apply,smul_apply,inner_sub_right,inner_smul_right]
  rw [ee,el,er]
  simp only [one_mul,map_one,mul_one]
  ring

theorem weakOperator_affine (r : ℝ) (j : Fin n) (c d : ℂ)
    (x : I → Fock n) (y : J → Fock n) (z : K → Fock n)
    (hx : Summable (fun i => ‖x i‖^2)) (hy : Summable (fun j => ‖y j‖^2))
    (hz : Summable (fun k => ‖z k‖^2))
    (he : CrossEnsemble.operator (baseFamily z) (baseFamily z)=
      c • CrossEnsemble.operator (baseFamily x) (baseFamily x)+
      d • CrossEnsemble.operator (baseFamily y) (baseFamily y)) :
    weakOperator r j z=c • weakOperator r j x+d • weakOperator r j y := by
  apply entry_ext
  intro k l
  have e (T U : Fock n →L[ℂ] Fock n) (a b : NumberIndex n) :
      entry (c • T+d • U) a b=c*entry T a b+d*entry U a b := by
    simp only [entry,add_apply,smul_apply,inner_add_right,inner_smul_right]
  rw [weakOperator_entry r j z hz,e,weakOperator_entry r j x hx,weakOperator_entry r j y hy,he]
  rw [e,e]
  ring

theorem weak_pairing_affine (r : ℝ) (j : Fin n) (c d : ℂ)
    (x : I → Fock n) (y : J → Fock n) (z : K → Fock n)
    (hx : Summable (fun i => ‖x i‖^2)) (hy : Summable (fun j => ‖y j‖^2))
    (hz : Summable (fun k => ‖z k‖^2))
    (he : CrossEnsemble.operator (baseFamily z) (baseFamily z)=
      c • CrossEnsemble.operator (baseFamily x) (baseFamily x)+
      d • CrossEnsemble.operator (baseFamily y) (baseFamily y)) (Z : Fock n →L[ℂ] Fock n) :
    singleWeak r j z Z=c*singleWeak r j x Z+d*singleWeak r j y Z := by
  let bas : HilbertBasis (NumberIndex n) ℂ (Fock n) := HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)
  apply (weak_pairing_hasSum bas r j z hz Z).unique
  rw [weakOperator_affine r j c d x y z hx hy hz he]
  simpa only [add_apply,smul_apply,map_add,map_smul,inner_add_right,inner_smul_right] using
    ((weak_pairing_hasSum bas r j x hx Z).mul_left c).add ((weak_pairing_hasSum bas r j y hy Z).mul_left d)

theorem weakOperator_zero_of_geometric_diagonal (r : ℝ) (p : NumberIndex n → ℝ)
    (hb : ∀ j k, (r+1:ℂ)*(p (up j k):ℂ)=(r:ℂ)*(p k:ℂ))
    (x : I → Fock n) (hx : Summable (fun i => ‖x i‖^2))
    (he : ∀ k l, entry (CrossEnsemble.operator (baseFamily x) (baseFamily x)) k l=
      if k=l then (p k:ℂ) else 0) (j : Fin n) : weakOperator r j x=0 := by
  apply entry_ext
  intro k l
  rw [weakOperator_entry r j x hx,he,he]
  simp only [entry, zero_apply, inner_zero_right]
  by_cases hk : k=up j l
  · subst k
    have hc : raiseCoefficient j (up j l)=conj (lowerCoefficient j l) := by
      simp [raiseCoefficient, lowerCoefficient, up_same]
    rw [ite_eq_left rfl,down_up,ite_eq_left rfl,hc]
    calc
      _ = conj (lowerCoefficient j l)*((r+1:ℂ)*(p (up j l):ℂ)-(r:ℂ)*(p l:ℂ)) := by ring
      _ = 0 := by rw [hb]; ring
  · rw [ite_eq_right hk,mul_zero,zero_sub]
    by_cases hz : k j=0
    · simp [raiseCoefficient,hz]
    · have hd : down j k≠l := by
        intro h
        apply hk
        rw [← h,up_down j k (Nat.pos_of_ne_zero hz)]
      rw [ite_eq_right hd,mul_zero,neg_zero]

theorem weak_thermal_pairing_zero (r : ℝ) (hr : 0<r)
    (x : I → Fock n) (hx : Summable (fun i => ‖x i‖^2))
    (he : ∀ k l, entry (CrossEnsemble.operator (baseFamily x) (baseFamily x)) k l=
      if k=l then (thermalWeight n r k:ℂ) else 0) (j : Fin n) (Z : Fock n →L[ℂ] Fock n) :
    singleWeak r j x Z=0 := by
  let bas : HilbertBasis (NumberIndex n) ℂ (Fock n) := HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)
  have hh := weak_pairing_hasSum bas r j x hx Z
  have he0 := weakOperator_zero_of_geometric_diagonal r (thermalWeight n r) (fun j k => by simpa only [Complex.ofReal_add, Complex.ofReal_one] using thermalWeight_balance r hr j k) x hx he j
  have hzero : HasSum (fun _ : NumberIndex n => (0:ℂ)) 0 := hasSum_zero
  have hz : HasSum (fun _ : NumberIndex n => (0:ℂ)) (singleWeak r j x Z) := by
    simpa only [he0,zero_apply,map_zero,inner_zero_right] using hh
  exact hz.unique hzero
end PhysicalGenerator

namespace EntropyPhotonNumber
open QuantumTrace Annihilation BeamLadder TensorLp
namespace WeightedColumns
variable {n : ℕ} {ρ : State n} (X : WeightedColumns ρ)

def rawSlice (η : ℝ) (hη : η ∈ Set.Icc 0 1) (Z : Fock n →L[ℂ] Fock n) : Fock n →L[ℂ] Fock n :=
  conditionalLeft (fun i => inverseWeight 3 (X.vector i)) X.normalized (conjugate η hη Z)

def rawSliceRight (η : ℝ) (hη : η ∈ Set.Icc 0 1) (Z : Fock n →L[ℂ] Fock n) : Fock n →L[ℂ] Fock n :=
  conditionalRight (fun i => inverseWeight 3 (X.vector i)) X.normalized (conjugate η hη Z)

theorem thermal_weak_zero (r : ℝ) (hr : 0<r)
    (he : ∀ k l, entry ρ.op k l=if k=l then (thermalWeight n r k:ℂ) else 0)
    (j : Fin n) (Z : Fock n →L[ℂ] Fock n) : singleWeak r j X.vector Z=0 := by
  apply PhysicalGenerator.weak_thermal_pairing_zero r hr X.vector X.summable
  intro k l
  rw [X.base_density,he]
end WeightedColumns

theorem replaced_threeport_weak
    {n : ℕ} (η θ κ a b d : ℝ) (hη : η ∈ Set.Icc 0 1) (hθ : θ ∈ Set.Icc 0 1)
    (ρ σ τD m γ ω ρ0 : State n)
    (h1 : IsBeamSplitterOutput η ρ σ m) (h2 : IsBeamSplitterOutput θ m τD γ)
    (X : WeightedColumns ρ) (Y : WeightedColumns σ) (D : WeightedColumns τD)
    (M : WeightedColumns m) (G : WeightedColumns γ) (O : WeightedColumns ω) (R : WeightedColumns ρ0)
    (hd : 0<d) (hr0 : 0<θ*(η*a+(1-η)*b)+(1-θ)*d)
    (hD : ∀ k l, entry τD.op k l=if k=l then (thermalWeight n d k:ℂ) else 0)
    (hO : ∀ k l, entry ω.op k l=if k=l then (thermalWeight n (θ*(η*a+(1-η)*b)+(1-θ)*d) k:ℂ) else 0)
    (hrepl : ρ0.op=((1-κ:ℝ):ℂ) • γ.op+(κ:ℂ) • ω.op)
    (j : Fin n) (Z : Fock n →L[ℂ] Fock n) :
    singleWeak (θ*(η*a+(1-η)*b)+(1-θ)*d) j R.vector Z=
      ((1-κ:ℝ):ℂ)*((Real.sqrt θ:ℂ)*(Real.sqrt η:ℂ)*
        singleWeak a j X.vector (Y.rawSlice η hη (D.rawSlice θ hθ Z))+
        (Real.sqrt θ:ℂ)*(Real.sqrt (1-η):ℂ)*
        singleWeak b j Y.vector (X.rawSliceRight η hη (D.rawSlice θ hθ Z))) := by
  have hr := PhysicalGenerator.weak_pairing_affine
    (θ*(η*a+(1-η)*b)+(1-θ)*d) j ((1-κ:ℝ):ℂ) (κ:ℂ)
    G.vector O.vector R.vector G.summable O.summable R.summable
    (by rw [G.base_density,O.base_density,R.base_density,hrepl]) Z
  rw [hr,O.thermal_weak_zero _ hr0 hO,mul_zero,add_zero]
  have hh2 := physical_product_weak θ (η*a+(1-η)*b) d hθ m τD γ h2 j
    M.vector D.vector G.vector M.summable D.summable G.summable M.normalized D.normalized
    M.density D.density G.density Z
  have hh1 := physical_product_weak η a b hη ρ σ m h1 j
    X.vector Y.vector M.vector X.summable Y.summable M.summable X.normalized Y.normalized
    X.density Y.density M.density (D.rawSlice θ hθ Z)
  change singleWeak (θ*(η*a+(1-η)*b)+(1-θ)*d) j G.vector Z=
    (Real.sqrt θ:ℂ)*singleWeak (η*a+(1-η)*b) j M.vector (D.rawSlice θ hθ Z)+
    (Real.sqrt (1-θ):ℂ)*singleWeak d j D.vector (M.rawSliceRight θ hθ Z) at hh2
  rw [D.thermal_weak_zero d hd hD,mul_zero,add_zero,hh1] at hh2
  rw [hh2]
  dsimp only [WeightedColumns.rawSlice,WeightedColumns.rawSliceRight]
  ring
end EntropyPhotonNumber

namespace KrausBounded
variable {E H I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
theorem dual_one (V : I → E →L[ℂ] H) (hV : ∀ x, HasSum (fun i => ‖V i x‖^2) (‖x‖^2)) :
    dual V hV (1 : H →L[ℂ] H)=1 := by
  apply ContinuousLinearMap.coe_injective
  apply (ext_inner_map _ _).mp
  intro x
  have hh := dual_entry V hV 1 x x
  have hs : HasSum (fun i => inner ℂ (V i x) (V i x)) (inner ℂ x x) := by
    convert! (hV x).mapL Complex.ofRealCLM using 1 <;>
      simp only [inner_self_eq_norm_sq_to_K,Complex.ofReal_pow,Complex.ofRealCLM_apply]
    all_goals rfl
  have he : inner ℂ x (dual V hV 1 x)=inner ℂ x x := hh.unique (by simpa only [one_apply_eq_self] using hs)
  simpa only [inner_conj_symm,ContinuousLinearMap.coe_coe,one_apply_eq_self] using
    congrArg (starRingEnd ℂ) he
end KrausBounded

namespace BeamLadder
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ}
theorem conjugate_one (η : ℝ) (hη : η ∈ Set.Icc 0 1) :
    conjugate (n:=n) η hη 1=1 := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [conjugate,liftLeft_one,ContinuousLinearMap.comp_apply,one_apply_eq_self]
  change (beamUnitary η hη).symm (beamUnitary η hη x)=x
  exact (beamUnitary η hη).symm_apply_apply x
end BeamLadder

namespace EntropyPhotonNumber
open QuantumTrace Annihilation BeamLadder TensorLp
namespace WeightedColumns
variable {n : ℕ} {ρ : State n} (X : WeightedColumns ρ)

def expectation (Z : Fock n →L[ℂ] Fock n) : ℂ :=
  CrossEnsemble.pairing (fun i => inverseWeight 3 (X.vector i))
    (fun i => inverseWeight 3 (X.vector i)) Z

def weakMean (r : ℝ) (j : Fin n) : ℂ := singleWeak r j X.vector 1

def centeredWeak (r : ℝ) (j : Fin n) (Z : Fock n →L[ℂ] Fock n) : ℂ :=
  singleWeak r j X.vector Z-X.weakMean r j*X.expectation Z

theorem expectation_one : X.expectation 1=1 := by
  have hh := X.normalized.mapL Complex.ofRealCLM
  unfold expectation CrossEnsemble.pairing
  have hs : HasSum (fun i => inner ℂ (inverseWeight 3 (X.vector i))
      ((1 : Fock n →L[ℂ] Fock n) (inverseWeight 3 (X.vector i)))) (1:ℂ) := by
    convert! hh using 1
    ext i
    simp only [one_apply_eq_self,inner_self_eq_norm_sq_to_K,Complex.ofRealCLM_apply,Complex.ofReal_pow]
    rfl
  exact hs.tsum_eq

theorem centeredWeak_one (r : ℝ) (j : Fin n) : X.centeredWeak r j 1=0 := by
  simp only [centeredWeak,weakMean,X.expectation_one,mul_one,sub_self]

theorem rawSlice_one (η : ℝ) (hη : η ∈ Set.Icc 0 1) : X.rawSlice η hη 1=1 := by
  simp only [rawSlice,conjugate_one,conditionalLeft,KrausBounded.dual_one]

theorem rawSliceRight_one (η : ℝ) (hη : η ∈ Set.Icc 0 1) : X.rawSliceRight η hη 1=1 := by
  simp only [rawSliceRight,conjugate_one,conditionalRight,KrausBounded.dual_one]

theorem expectation_affine {σ τ : State n} (Y : WeightedColumns σ) (Z : WeightedColumns τ)
    (c d : ℂ) (he : τ.op=c • ρ.op+d • σ.op) (A : Fock n →L[ℂ] Fock n) :
    Z.expectation A=c*X.expectation A+d*Y.expectation A := by
  let bas : HilbertBasis (NumberIndex n) ℂ (Fock n) := HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)
  have hx := CrossEnsemble.pairing_trace bas X.normalized.summable X.normalized.summable A
  have hy := CrossEnsemble.pairing_trace bas Y.normalized.summable Y.normalized.summable A
  have hz := CrossEnsemble.pairing_trace bas Z.normalized.summable Z.normalized.summable A
  change HasSum (fun k => inner ℂ (bas k) (A (TraceEnsemble.operator
    (fun i => inverseWeight 3 (X.vector i)) (bas k)))) (X.expectation A) at hx
  rw [X.density] at hx
  change HasSum (fun k => inner ℂ (bas k) (A (TraceEnsemble.operator
    (fun i => inverseWeight 3 (Y.vector i)) (bas k)))) (Y.expectation A) at hy
  rw [Y.density] at hy
  change HasSum (fun k => inner ℂ (bas k) (A (TraceEnsemble.operator
    (fun i => inverseWeight 3 (Z.vector i)) (bas k)))) (Z.expectation A) at hz
  rw [Z.density] at hz
  exact hz.unique (by
    simpa only [he,add_apply,smul_apply,map_add,map_smul,inner_add_right,inner_smul_right] using
      (hx.mul_left c).add (hy.mul_left d))
end WeightedColumns

theorem physical_rawSlice_expectation {n : ℕ} (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    (ρ σ τ : State n) (hτ : IsBeamSplitterOutput η ρ σ τ)
    (X : WeightedColumns ρ) (Y : WeightedColumns σ) (T : WeightedColumns τ)
    (Z : Fock n →L[ℂ] Fock n) :
    X.expectation (Y.rawSlice η hη Z)=T.expectation Z ∧
      Y.expectation (X.rawSliceRight η hη Z)=T.expectation Z := by
  let v := fun i => inverseWeight 3 (X.vector i)
  let w := fun j => inverseWeight 3 (Y.vector j)
  let U := fun ij : X.Index × Y.Index => beamUnitary η hη (tensor (v ij.1) (w ij.2))
  have hu : Summable (fun ij => ‖U ij‖^2) := by
    simpa only [U,LinearIsometryEquiv.norm_map] using
      tensorFamily_summable v w X.normalized.summable Y.normalized.summable
  have hd := physical_ensemble_output η hη ρ σ τ hτ v w X.normalized Y.normalized X.density Y.density
  have hs := slice_family_summable U hu
  have he : CrossEnsemble.operator (fun ie : (X.Index × Y.Index) × NumberIndex n => slice (U ie.1) ie.2)
      (fun ie : (X.Index × Y.Index) × NumberIndex n => slice (U ie.1) ie.2)=
    CrossEnsemble.operator (fun i => inverseWeight 3 (T.vector i)) (fun i => inverseWeight 3 (T.vector i)) := by
    rw [cross_slice_eq_partialTrace]
    change partialTrace U=TraceEnsemble.operator _
    rw [T.density]
    exact hd
  let bas : HilbertBasis (NumberIndex n) ℂ (Fock n) := HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)
  have hp := CrossEnsemble.pairing_eq_of_operator_eq bas hs hs T.normalized.summable T.normalized.summable he Z
  have hpair : CrossEnsemble.pairing (fun ij : X.Index × Y.Index => tensor (v ij.1) (w ij.2))
      (fun ij : X.Index × Y.Index => tensor (v ij.1) (w ij.2)) (conjugate η hη Z)=T.expectation Z := by
    calc
      _ = CrossEnsemble.pairing U U (liftLeft Z) := by
        unfold CrossEnsemble.pairing
        congr 1
        funext ij
        exact conjugate_inner η hη Z _ _
      _ = _ := (pairing_liftLeft U U hu hu Z).trans hp
  constructor
  · rw [← hpair]
    exact (pairing_conditionalLeft v v w X.normalized.summable X.normalized.summable Y.normalized
      (conjugate η hη Z)).symm
  · rw [← hpair]
    exact (pairing_conditionalRight v w w X.normalized Y.normalized.summable Y.normalized.summable
      (conjugate η hη Z)).symm

theorem replaced_threeport_centered_weak
    {n : ℕ} (η θ κ a b d : ℝ) (hη : η ∈ Set.Icc 0 1) (hθ : θ ∈ Set.Icc 0 1)
    (ρ σ τD m γ ω ρ0 : State n)
    (h1 : IsBeamSplitterOutput η ρ σ m) (h2 : IsBeamSplitterOutput θ m τD γ)
    (X : WeightedColumns ρ) (Y : WeightedColumns σ) (D : WeightedColumns τD)
    (M : WeightedColumns m) (G : WeightedColumns γ) (O : WeightedColumns ω) (R : WeightedColumns ρ0)
    (hd : 0<d) (hr0 : 0<θ*(η*a+(1-η)*b)+(1-θ)*d)
    (hD : ∀ k l, entry τD.op k l=if k=l then (thermalWeight n d k:ℂ) else 0)
    (hO : ∀ k l, entry ω.op k l=if k=l then (thermalWeight n (θ*(η*a+(1-η)*b)+(1-θ)*d) k:ℂ) else 0)
    (hrepl : ρ0.op=((1-κ:ℝ):ℂ) • γ.op+(κ:ℂ) • ω.op)
    (j : Fin n) (Z : Fock n →L[ℂ] Fock n) :
    R.centeredWeak (θ*(η*a+(1-η)*b)+(1-θ)*d) j Z=
      ((1-κ:ℝ):ℂ)*((Real.sqrt θ:ℂ)*(Real.sqrt η:ℂ)*
        X.centeredWeak a j (Y.rawSlice η hη (D.rawSlice θ hθ Z))+
        (Real.sqrt θ:ℂ)*(Real.sqrt (1-η):ℂ)*
        Y.centeredWeak b j (X.rawSliceRight η hη (D.rawSlice θ hθ Z)))+
      (κ:ℂ)*((1-κ:ℝ):ℂ)*G.weakMean (θ*(η*a+(1-η)*b)+(1-θ)*d) j*
        (G.expectation Z-O.expectation Z) := by
  let r0 := θ*(η*a+(1-η)*b)+(1-θ)*d
  have hp (A : Fock n →L[ℂ] Fock n) := replaced_threeport_weak η θ κ a b d hη hθ
    ρ σ τD m γ ω ρ0 h1 h2 X Y D M G O R hd hr0 hD hO hrepl j A
  have hg (A : Fock n →L[ℂ] Fock n) := replaced_threeport_weak η θ 0 a b d hη hθ
    ρ σ τD m γ ω γ h1 h2 X Y D M G O G hd hr0 hD hO (by
      simp only [sub_zero,Complex.ofReal_one,Complex.ofReal_zero,one_smul]
      apply ContinuousLinearMap.ext
      intro vector
      simp only [add_apply,smul_apply,zero_smul,add_zero]) j A
  have hmG : G.weakMean r0 j=(Real.sqrt θ:ℂ)*(Real.sqrt η:ℂ)*X.weakMean a j+
      (Real.sqrt θ:ℂ)*(Real.sqrt (1-η):ℂ)*Y.weakMean b j := by
    simpa only [WeightedColumns.weakMean,WeightedColumns.rawSlice_one,WeightedColumns.rawSliceRight_one,
      sub_zero,Complex.ofReal_one,one_mul] using hg 1
  have hmR : R.weakMean r0 j=((1-κ:ℝ):ℂ)*G.weakMean r0 j := by
    rw [hmG]
    simpa only [WeightedColumns.weakMean,WeightedColumns.rawSlice_one,WeightedColumns.rawSliceRight_one] using hp 1
  have he2 := (physical_rawSlice_expectation θ hθ m τD γ h2 M D G Z).1
  have he1 := physical_rawSlice_expectation η hη ρ σ m h1 X Y M (D.rawSlice θ hθ Z)
  have hex := he1.1.trans he2
  have hey := he1.2.trans he2
  have her := G.expectation_affine O R ((1-κ:ℝ):ℂ) (κ:ℂ) hrepl Z
  change R.centeredWeak r0 j Z=_
  unfold WeightedColumns.centeredWeak
  rw [hp,hmR,her,hex,hey,hmG]
  simp only [Complex.ofReal_sub,Complex.ofReal_one]
  ring
end EntropyPhotonNumber

namespace BeamLadder
open EntropyPhotonNumber QuantumTrace Annihilation
open scoped ComplexConjugate
variable {n : ℕ}

theorem single_ladder_inner (j : Fin n) (x y : Fock n) :
    inner ℂ (sandwich 0 3 (by omega) j x) (inverseWeight 3 y)=
      inner ℂ (inverseWeight 3 x) (creationSandwich 0 3 (by omega) j y) := by
  have hz (k : NumberIndex n) (hk : k ∉ Set.range (up j)) :
      inner ℂ (inverseWeight 3 x k) (creationSandwich 0 3 (by omega) j y k)=0 := by
    have hkj : k j=0 := by
      by_contra hne
      exact hk ⟨down j k,up_down j k (Nat.pos_of_ne_zero hne)⟩
    rw [creationSandwich_zero _ _ _ _ _ _ hkj,inner_zero_right]
  have hh := (up_injective j).hasSum_iff hz |>.mpr
    (lp.hasSum_inner (𝕜:=ℂ) (inverseWeight 3 x) (creationSandwich 0 3 (by omega) j y))
  apply HasSum.unique (lp.hasSum_inner (𝕜:=ℂ) (sandwich 0 3 (by omega) j x) (inverseWeight 3 y))
  convert! hh using 1
  ext k
  simp only [Function.comp_def,RCLike.inner_apply,single_lower_third_apply,
    single_raise_third_apply,up_same,down_up,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,
    ↓reduceIte,Nat.cast_add,Nat.cast_one,map_mul,Complex.conj_ofReal]
  ring
end BeamLadder

namespace EntropyPhotonNumber

namespace WeightedColumns
open QuantumTrace Annihilation BeamLadder
variable {n : ℕ} {ρ : State n} (X : WeightedColumns ρ)

theorem weakMean_trace (r : ℝ) (j : Fin n) :
    X.weakMean r j=∑' i, inner ℂ (sandwich 0 3 (by omega) j (X.vector i))
      (inverseWeight 3 (X.vector i)) := by
  have he : CrossEnsemble.pairing (fun i => creationSandwich 0 3 (by omega) j (X.vector i))
      (fun i => inverseWeight 3 (X.vector i)) 1=
    CrossEnsemble.pairing (fun i => inverseWeight 3 (X.vector i))
      (fun i => sandwich 0 3 (by omega) j (X.vector i)) 1 := by
    unfold CrossEnsemble.pairing
    apply tsum_congr
    intro i
    simpa only [one_apply_eq_self] using (single_ladder_inner j (X.vector i) (X.vector i)).symm
  unfold weakMean singleWeak
  rw [he]
  simp only [CrossEnsemble.pairing,one_apply_eq_self]
  ring

theorem weakMean_reference (a b : ℝ) (j : Fin n) : X.weakMean a j=X.weakMean b j := by
  rw [X.weakMean_trace,X.weakMean_trace]
end WeightedColumns

def MainObligation : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (ρA ρB ρC : State n),
    FiniteEnergy ρA → FiniteEnergy ρB → ∀ η : ℝ, η ∈ Set.Icc 0 1 →
    IsBeamSplitterOutput η ρA ρB ρC →
    η * gInv (entropy ρA / n) + (1 - η) * gInv (entropy ρB / n) ≤
      gInv (entropy ρC / n)

end EntropyPhotonNumber

end

end OAI
