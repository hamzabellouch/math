import OAI.Analysis.GroupDeterminants.WeightedProjections

namespace OAI

universe uR uG uF uS uH

noncomputable section
open scoped BigOperators

namespace GroupRingDeterminant

section GroupStar
variable {R : Type uR} {G : Type uG} [Semiring R] [StarRing R] [Group G]

def groupStar (a : MonoidAlgebra R G) : MonoidAlgebra R G :=
  MonoidAlgebra.mapDomainAddEquiv R (Equiv.inv G)
    (MonoidAlgebra.map (starAddEquiv : R ≃+ R).toAddMonoidHom a)

@[simp] lemma groupStar_coeff (a : MonoidAlgebra R G) (g : G) :
    (groupStar a).coeff g = star (a.coeff g⁻¹) := by
  simp [groupStar, MonoidAlgebra.coeff_mapDomainAddEquiv]

@[simp] lemma groupStar_single (g : G) (r : R) :
    groupStar (MonoidAlgebra.single g r) = MonoidAlgebra.single g⁻¹ (star r) := by
  classical
  ext h
  simp only [groupStar_coeff, MonoidAlgebra.coeff_single]
  by_cases hh : g = h⁻¹
  · have he : g⁻¹ = h := by rw [hh, inv_inv]
    simp [hh]
  · have he : g⁻¹ ≠ h := fun he => hh (by rw [← he, inv_inv])
    simp [hh, he]

@[simp] lemma groupStar_zero : groupStar (0 : MonoidAlgebra R G) = 0 := by ext; simp

@[simp] lemma groupStar_add (a b : MonoidAlgebra R G) :
    groupStar (a + b) = groupStar a + groupStar b := by ext; simp

@[simp] lemma groupStar_star (a : MonoidAlgebra R G) : groupStar (groupStar a) = a := by ext; simp

lemma groupStar_mul (a b : MonoidAlgebra R G) : groupStar (a * b) = groupStar b * groupStar a := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [add_mul, groupStar_add, ha, hb, mul_add]
  | single g r =>
    induction b using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [mul_add, groupStar_add, ha, hb, add_mul]
    | single h s => simp [MonoidAlgebra.single_mul_single]

instance groupAlgebraStar : StarRing (MonoidAlgebra R G) where
  star := groupStar
  star_involutive := groupStar_star
  star_mul := groupStar_mul
  star_add := groupStar_add

@[simp] lemma star_groupAlgebra_coeff (a : MonoidAlgebra R G) (g : G) :
    (star a).coeff g = star (a.coeff g⁻¹) := groupStar_coeff a g

@[simp] lemma star_groupAlgebra_single (g : G) (r : R) :
    star (MonoidAlgebra.single g r) = MonoidAlgebra.single g⁻¹ (star r) := groupStar_single g r

instance groupAlgebraStarModule {F : Type uF} [CommSemiring F] [StarRing F]
    [Algebra F R] [StarModule F R] : StarModule F (MonoidAlgebra R G) where
  star_smul c a := by ext; simp

variable {S : Type uS} [Semiring S] [StarRing S]
lemma groupAlgebra_map_star (f : R →+* S) (hf : ∀ r, f (star r) = star (f r))
    (a : MonoidAlgebra R G) :
    MonoidAlgebra.mapRingHom G f (star a) = star (MonoidAlgebra.mapRingHom G f a) := by
  ext g
  simp [hf]

variable {H : Type uH} [Group H]
lemma groupAlgebra_mapDomain_star (f : G →* H) (a : MonoidAlgebra R G) :
    MonoidAlgebra.mapDomainRingHom R f (star a) = star (MonoidAlgebra.mapDomainRingHom R f a) := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [star_add, map_add, ha, hb]
  | single g r => simp

end GroupStar

end GroupRingDeterminant

end

end OAI
