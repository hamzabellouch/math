import OAI.Algebra.OddKaplansky.OrderedCoordinates

namespace OAI

universe contextUniverse1

universe portUniverse1 portUniverse2 portUniverse3

section
namespace OddKaplansky.OrderedCosetMatrix
noncomputable section
open scoped Classical BigOperators Matrix
variable {K : Type portUniverse1} {G : Type portUniverse2} [Field K] [Group G] [sectionInstance60 : Fintype G] [sectionInstance61 : LinearOrder G] (T : Subgroup G)
local instance orderedMatrixDecidableEq : DecidableEq G := Classical.decEq G
abbrev Q := G ⧸ T
abbrev D := MonoidAlgebra K T
open OrderedCosetCoordinates
lemma mk_left
    {G : Type contextUniverse1}
    [contextInstance1 : Group.{contextUniverse1} G]
    [Fintype.{contextUniverse1} G]
    [LinearOrder.{contextUniverse1} G]
    (T : @Subgroup.{contextUniverse1} G contextInstance1) (g h : G) : ((g*h : G) : G ⧸ T) = g • (h : G ⧸ T) := rfl
lemma mk_mul_rep (g : G) (q : G ⧸ T) : ((g*rep T q : G) : G ⧸ T) = g • q := by rw [mk_left,rep_mk]
def cocycle (g : G) (q : G ⧸ T) : T := residue T (g * rep T q)
lemma cocycle_reconstruct (g : G) (q : G ⧸ T) : rep T (g • q) * (cocycle T g q : G) = g*rep T q := by
  simpa only [cocycle,mk_mul_rep] using reconstruct T (g*rep T q)
lemma cocycle_one (q : G ⧸ T) : cocycle T 1 q = 1 := by
  apply Subtype.ext
  simp [cocycle,residue,rep_mk]
lemma cocycle_mul (g h : G) (q : G ⧸ T) : cocycle T (g*h) q = cocycle T g (h • q) * cocycle T h q := by
  apply Subtype.ext
  apply mul_left_cancel (a := rep T ((g*h) • q))
  rw [cocycle_reconstruct,Subgroup.coe_mul,mul_smul,← mul_assoc,cocycle_reconstruct]
  simp only [mul_assoc,cocycle_reconstruct]

def groupMatrix (g : G) : Matrix (G ⧸ T) (G ⧸ T) (D (K := K) T) := fun q r =>
  if q = g • r then MonoidAlgebra.single (cocycle T g r) 1 else 0
lemma groupMatrix_one : groupMatrix (K := K) T 1 = 1 := by
  funext q r
  simp [groupMatrix,Matrix.one_apply,cocycle_one,MonoidAlgebra.one_def]
lemma groupMatrix_mul (g h : G) : groupMatrix (K := K) T (g*h) = groupMatrix T g * groupMatrix T h := by
  ext q r
  rw [Matrix.mul_apply,Finset.sum_eq_single (h • r)]
  · simp only [groupMatrix,ite_true,ite_mul,zero_mul,      MonoidAlgebra.single_mul_single,one_mul,cocycle_mul,mul_smul]
  · intro z _ hz
    simp [groupMatrix,hz]
  · simp
def representation : MonoidAlgebra K G →ₐ[K] Matrix (G ⧸ T) (G ⧸ T) (D (K := K) T) :=
  MonoidAlgebra.lift K _ G { toFun := groupMatrix T, map_one' := groupMatrix_one T, map_mul' := groupMatrix_mul T }
lemma representation_single (g : G) (c : K) : representation T (MonoidAlgebra.single g c) = c • groupMatrix T g := by
  simp [representation]

def coefficients {X : Type portUniverse3} [Finite X] : MonoidAlgebra K X ≃ₗ[K] (X → K) :=
  (MonoidAlgebra.coeffLinearEquiv K).trans (Finsupp.linearEquivFunOnFinite K K X)
def unpack : ((G ⧸ T) → D (K := K) T) ≃ₗ[K] MonoidAlgebra K G :=
  (LinearEquiv.piCongrRight (fun _ : G ⧸ T => coefficients)).trans
    ((LinearEquiv.curry K K (G ⧸ T) T).symm.trans
      ((LinearEquiv.piCongrLeft K (fun _ : (G ⧸ T) × T => K) (equiv T)).symm.trans coefficients.symm))
lemma unpack_coeff (v : (G ⧸ T) → D (K := K) T) (g : G) :
    (unpack T v).coeff g = (v (g : G ⧸ T)).coeff (residue T g) := rfl
lemma unpack_symm_coeff (v : MonoidAlgebra K G) (q : G ⧸ T) (t : T) :
    ((unpack T).symm v q).coeff t = v.coeff (rep T q * t) := by
  have h := unpack_coeff T ((unpack T).symm v) (rep T q * t)
  rw [LinearEquiv.apply_symm_apply,mk_rep_mul,residue_rep_mul] at h
  exact h.symm
lemma unpack_basis (q : G ⧸ T) (t : T) :
    unpack (K := K) T (Pi.single q (MonoidAlgebra.single t 1)) = MonoidAlgebra.single (rep T q * t) 1 := by
  apply (unpack T).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  funext r
  apply MonoidAlgebra.coeff_injective
  ext s
  rw [unpack_symm_coeff]
  by_cases h : r=q
  · subst r
    simp [MonoidAlgebra.coeff_single,Finsupp.single_apply]
  · have hn : rep T r*(s : G) ≠ rep T q*(t : G) := by
      intro he
      have hq := congrArg (fun g : G => (g : G ⧸ T)) he
      rw [mk_rep_mul,mk_rep_mul] at hq
      exact h hq
    simp [Pi.single_eq_of_ne h,MonoidAlgebra.coeff_single,hn]
lemma residue_left (g x : G) : residue T (g*x) = cocycle T g (x : G ⧸ T) * residue T x := by
  apply Subtype.ext
  apply mul_left_cancel (a := rep T ((g*x : G) : G ⧸ T))
  rw [reconstruct,Subgroup.coe_mul,mk_left,← mul_assoc,cocycle_reconstruct,mul_assoc,reconstruct]
lemma groupMatrix_mulVec (g : G) (v : (G ⧸ T) → D (K := K) T) (q : G ⧸ T) :
    (groupMatrix T g).mulVec v q = MonoidAlgebra.single (cocycle T g (g⁻¹ • q)) 1 * v (g⁻¹ • q) := by
  rw [Matrix.mulVec, dotProduct,Finset.sum_eq_single (g⁻¹ • q)]
  · simp [groupMatrix]
  · intro r _ hr
    have hne : q ≠ g • r := by
      intro he
      apply hr
      rw [he,inv_smul_smul]
    simp [groupMatrix,hne]
  · simp
lemma unpack_group (g : G) (v : (G ⧸ T) → D (K := K) T) :
    unpack T ((groupMatrix T g).mulVec v) = MonoidAlgebra.single g 1 * unpack T v := by
  apply MonoidAlgebra.coeff_injective
  ext x
  rw [unpack_coeff,groupMatrix_mulVec,MonoidAlgebra.coeff_single_mul_apply,
    MonoidAlgebra.coeff_single_mul_apply,unpack_coeff,one_mul,one_mul]
  have hq : ((g⁻¹*x : G) : G ⧸ T) = g⁻¹ • (x : G ⧸ T) := rfl
  have hr := residue_left T g (g⁻¹*x)
  simp only [mul_inv_cancel_left,hq] at hr
  rw [hq,hr,inv_mul_cancel_left]
lemma unpack_representation (e : MonoidAlgebra K G) (v : (G ⧸ T) → D (K := K) T) :
    unpack T ((representation T e).mulVec v) = e * unpack T v := by
  induction e using MonoidAlgebra.induction_on with
  | of g => simpa only [MonoidAlgebra.of_apply,representation_single,one_smul] using unpack_group T g v
  | add e f he hf => simp only [map_add,Matrix.add_mulVec,he,hf,add_mul]
  | smul c e he => simp only [map_smul,Matrix.smul_mulVec,map_smul,he,smul_mul_assoc]

section Commutative
variable [IsMulCommutative T]
local instance orderedMatrixCommGroup : CommGroup T := { (inferInstance : Group T) with mul_comm := mul_comm' }
def endomorphism (e : MonoidAlgebra K G) : Module.End (D (K := K) T) ((G ⧸ T) → D (K := K) T) :=
  Matrix.toLin' (representation T e)
lemma endomorphism_idempotent (e : MonoidAlgebra K G) (he : e*e=e) :
    endomorphism T e * endomorphism T e = endomorphism T e := by
  change (Matrix.toLin' (representation T e)).comp (Matrix.toLin' (representation T e)) = Matrix.toLin' (representation T e)
  rw [← Matrix.toLin'_mul,← map_mul,he]
lemma endomorphism_rank (e : MonoidAlgebra K G) :
    Module.finrank K (LinearMap.range (endomorphism T e)) =
      Module.finrank K (LinearMap.range (Algebra.lmul K (MonoidAlgebra K G) e)) := by
  have ht : (unpack (K := K) T).toLinearMap.comp ((endomorphism T e).restrictScalars K) =
      (Algebra.lmul K (MonoidAlgebra K G) e).comp (unpack T).toLinearMap := by
    apply LinearMap.ext
    intro v
    exact unpack_representation T e v
  have hr := congrArg LinearMap.range ht
  rw [LinearMap.range_comp,LinearMap.range_comp,LinearEquiv.range,Submodule.map_top] at hr
  have hd := LinearEquiv.finrank_map_eq (unpack (K := K) T) (LinearMap.range ((endomorphism T e).restrictScalars K))
  rw [hr] at hd
  rw [LinearMap.range_restrictScalars] at hd
  have hx := ((Submodule.restrictScalarsEquiv K (D (K := K) T) _ (LinearMap.range (endomorphism T e))).restrictScalars K).finrank_eq
  exact hx.symm.trans hd.symm
end Commutative
end
end OddKaplansky.OrderedCosetMatrix

end

end OAI
