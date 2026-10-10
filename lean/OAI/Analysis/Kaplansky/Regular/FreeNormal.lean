import OAI.Analysis.Kaplansky.Main
import OAI.Analysis.Kaplansky.Regular.FreeFamily

namespace OAI

noncomputable section

namespace KaplanskyConsequences.Regular

attribute [local instance] Classical.decEq Classical.propDecidable

def translate (n : ℤ) : FZ ≃* FZ := FreeGroup.freeGroupCongr (Equiv.addRight n)
@[simp] lemma translate_of (n i : ℤ) : translate n (FreeGroup.of i) = FreeGroup.of (i+n) := by
  simp [translate,FreeGroup.freeGroupCongr]
lemma translate_zero (w : FZ) : translate 0 w = w := by
  have he : (translate 0).toMonoidHom = MonoidHom.id FZ := by
    apply FreeGroup.ext_hom; intro i; simp
  exact DFunLike.congr_fun he w
lemma translate_add (n m : ℤ) (w : FZ) : translate (n+m) w = translate n (translate m w) := by
  have he : (translate (n+m)).toMonoidHom = (translate n).toMonoidHom.comp (translate m).toMonoidHom := by
    apply FreeGroup.ext_hom; intro i; simp [add_comm,add_left_comm]
  exact DFunLike.congr_fun he w
lemma translate_one : translate 1 = shift := rfl
lemma translate_neg_one (w : FZ) : translate (-1) w = shift.symm w := by
  apply shift.injective
  rw [←translate_one,←translate_add]
  simpa using translate_zero w

def height : F2 →* Multiplicative ℤ := FreeGroup.lift (fun i => Multiplicative.ofAdd (if i=0 then 1 else 0))
def exponent (w : F2) : ℤ := (height w).toAdd
@[simp] lemma exponent_one : exponent 1 = 0 := by simp [exponent]
@[simp] lemma exponent_mul (w v : F2) : exponent (w*v) = exponent w + exponent v := by simp [exponent]
@[simp] lemma exponent_inv (w : F2) : exponent w⁻¹ = -exponent w := by simp [exponent]
@[simp] lemma exponent_a : exponent a = 1 := by simp [exponent,height,a]
@[simp] lemma exponent_b : exponent b = 0 := by simp [exponent,height,b]
@[simp] lemma coordinate_one : coordinate 1 = 1 := by simp [coordinate]
@[simp] lemma coordinate_a : coordinate a = 1 := by simp [coordinate]
@[simp] lemma coordinate_b : coordinate b = FreeGroup.of 0 := by simp [coordinate]
@[simp] lemma coordinate_a_inv : coordinate a⁻¹ = 1 := by simp [coordinate]
@[simp] lemma coordinate_b_inv : coordinate b⁻¹ = (FreeGroup.of 0)⁻¹ := by simp [coordinate]

lemma action_affine (w : F2) (v : FZ) : action w v = coordinate w * translate (exponent w) v := by
  induction w using FreeGroup.induction_on generalizing v with
  | one => simp [coordinate,translate_zero]
  | of i =>
    fin_cases i
    · change action a v = coordinate a * translate (exponent a) v
      simp [translate_one]
    · change action b v = coordinate b * translate (exponent b) v
      simp [translate_zero]
  | inv_of i ih =>
    fin_cases i
    · change action a⁻¹ v = coordinate a⁻¹ * translate (exponent a⁻¹) v
      simp [translate_neg_one]
    · change action b⁻¹ v = coordinate b⁻¹ * translate (exponent b⁻¹) v
      simp [translate_zero]
  | mul x y hx hy =>
    have hc : coordinate (x*y) = coordinate x * translate (exponent x) (coordinate y) := by
      simp only [coordinate,map_mul,Equiv.Perm.mul_apply]
      exact hx (action y 1)
    simp only [map_mul,Equiv.Perm.mul_apply,hx,hy,hc,exponent_mul,translate_add,map_mul,mul_assoc]

lemma coordinate_mul (x y : F2) :
    coordinate (x*y) = coordinate x * translate (exponent x) (coordinate y) := by
  simp only [coordinate,map_mul,Equiv.Perm.mul_apply]
  exact action_affine x (action y 1)

def genZ (n : ℤ) : F2 := a^n*b*a^(-n)
def kernelMap : FZ →* F2 := FreeGroup.lift genZ
@[simp] lemma kernelMap_of (n : ℤ) : kernelMap (FreeGroup.of n) = genZ n := by simp [kernelMap]
lemma kernelMap_translate (n : ℤ) (v : FZ) :
    kernelMap (translate n v) = a^n*kernelMap v*a^(-n) := by
  induction v using FreeGroup.induction_on with
  | one => simp
  | of i => simp [genZ,zpow_add]; group
  | inv_of i ih => simp only [map_inv]; rw [ih]; group
  | mul x y hx hy => rw [map_mul,map_mul,map_mul,hx,hy]; group

lemma normal_form (w : F2) : w = kernelMap (coordinate w) * a^(exponent w) := by
  induction w using FreeGroup.induction_on with
  | one => simp
  | of i =>
    fin_cases i
    · change a = kernelMap (coordinate a) * a^(exponent a); simp
    · change b = kernelMap (coordinate b) * a^(exponent b); simp [genZ]
  | inv_of i ih =>
    fin_cases i
    · change a⁻¹ = kernelMap (coordinate a⁻¹) * a^(exponent a⁻¹); simp
    · change b⁻¹ = kernelMap (coordinate b⁻¹) * a^(exponent b⁻¹); simp [genZ]
  | mul x y hx hy =>
    rw [coordinate_mul,map_mul,kernelMap_translate,exponent_mul,zpow_add]
    calc
      x*y = (kernelMap (coordinate x)*a^(exponent x))*(kernelMap (coordinate y)*a^(exponent y)) := by rw [←hx,←hy]
      _ = _ := by group

lemma coordinate_exponent_separate (w : F2) (hc : coordinate w=1) (he : exponent w=0) : w=1 := by
  simpa [hc,he] using normal_form w

lemma action_genZ (n : ℤ) : action (genZ n) = Equiv.mulLeft (FreeGroup.of n) := by
  have ha (k : ℤ) (v : FZ) : action (a^k) v = translate k v := by
    have hp : action a ^ k = (translate k).toEquiv := by
      induction k using Int.induction_on with
      | zero => ext v; simp [translate_zero]
      | succ k ih =>
        ext v
        rw [zpow_add,ih]
        simp only [zpow_one,action_a,Equiv.Perm.mul_apply]
        exact (translate_add k 1 v).symm
      | pred k ih =>
        ext v
        rw [zpow_sub,ih]
        simp only [zpow_one,action_a,Equiv.Perm.mul_apply]
        change translate (-(k:ℤ)) (shift.symm v) = translate (-(k:ℤ)-1) v
        rw [←translate_neg_one,←translate_add]
        rfl
    rw [map_zpow,hp]; rfl
  ext v
  simp only [genZ,map_mul,Equiv.Perm.mul_apply,ha,action_b]
  change translate n (FreeGroup.of 0 * translate (-n) v) = FreeGroup.of n * v
  rw [map_mul,translate_of,←translate_add]
  simp [translate_zero]

@[simp] lemma exponent_genZ (n : ℤ) : exponent (genZ n) = 0 := by
  simp [genZ,exponent,height,a,b]
@[simp] lemma coordinate_genZ (n : ℤ) : coordinate (genZ n) = FreeGroup.of n := by
  simp [coordinate,action_genZ]
lemma coordinate_genZ_mul (n : ℤ) (w : F2) : coordinate (genZ n*w) = FreeGroup.of n*coordinate w := by
  simp [coordinate_mul,translate_zero]


end KaplanskyConsequences.Regular

end

end OAI
