import Mathlib
import OAI.Combinatorics.SharpRamsey.Geometry.ScaledTangentDot

namespace OAI

/-! Incidence bounds for rich lines and finite point configurations. -/

section
section
section
section
namespace SharpLogRamsey.PolynomialCoordinates
open MvPolynomial
variable {K : Type*} [Field K]
noncomputable section
abbrev Triple := Polynomial (Polynomial (Polynomial K))

def encode : MvPolynomial (Fin 3) K ≃ₐ[K] Triple (K := K) :=
  (renameEquiv K (Equiv.swap 0 2)).trans ((finSuccEquiv K 2).trans
    (Polynomial.mapAlgEquiv ((finSuccEquiv K 1).trans
      (Polynomial.mapAlgEquiv (uniqueAlgEquiv K (Fin 1))))))

@[simp] lemma encode_C (a : K) : encode (C a) = Polynomial.C (Polynomial.C (Polynomial.C a)) := by
  simp [encode,finSuccEquiv_apply,uniqueAlgEquiv_apply]

@[simp] lemma encode_X (i : Fin 3) : encode (X i : MvPolynomial (Fin 3) K) =
    ![Polynomial.C (Polynomial.C Polynomial.X), Polynomial.C Polynomial.X, Polynomial.X] i := by
  have h2 : finSuccEquiv K 2 (X 2) = Polynomial.C (X 1) :=
    finSuccEquiv_X_succ (j := 1)
  have h1 : finSuccEquiv K 2 (X 1) = Polynomial.C (X 0) :=
    finSuccEquiv_X_succ (j := 0)
  have h11 : finSuccEquiv K 1 (X 1) = Polynomial.C (X 0) :=
    finSuccEquiv_X_succ (j := 0)
  fin_cases i <;> simp [encode,h2,h1,h11,finSuccEquiv_X_zero,
    uniqueAlgEquiv_apply,Equiv.swap_apply_def]

lemma encode_natDegree (F : MvPolynomial (Fin 3) K) :
    (encode F).natDegree ≤ F.totalDegree := by
  simp only [encode,AlgEquiv.trans_apply,Polynomial.coe_mapAlgEquiv]
  rw [Polynomial.natDegree_map_eq_of_injective (AlgEquiv.injective _),natDegree_finSuccEquiv]
  exact (degreeOf_le_totalDegree _ _).trans (totalDegree_rename_le _ _)

lemma coeff_degree_le {n : ℕ} (F : MvPolynomial (Fin (n+1)) K) (i : ℕ) :
    ((finSuccEquiv K n F).coeff i).totalDegree ≤ F.totalDegree := by
  by_cases h : (finSuccEquiv K n F).coeff i = 0
  · simp [h]
  · exact (Nat.le_add_right _ _).trans (totalDegree_coeff_finSuccEquiv_add_le F i h)

lemma encode_coeff_natDegree (F : MvPolynomial (Fin 3) K) (i : ℕ) :
    ((encode F).coeff i).natDegree ≤ F.totalDegree := by
  simp only [encode,AlgEquiv.trans_apply,Polynomial.coe_mapAlgEquiv,Polynomial.coeff_map]
  change (Polynomial.map (uniqueAlgEquiv K (Fin 1)).toRingHom
    (finSuccEquiv K 1 (((finSuccEquiv K 2) ((renameEquiv K (Equiv.swap 0 2)) F)).coeff i))).natDegree ≤ F.totalDegree
  rw [Polynomial.natDegree_map_eq_of_injective (AlgEquiv.injective _),natDegree_finSuccEquiv]
  exact (degreeOf_le_totalDegree _ _).trans
    ((coeff_degree_le _ i).trans (totalDegree_rename_le _ _))

def changeHom (a b c : K) : MvPolynomial (Fin 3) K →ₐ[K] MvPolynomial (Fin 3) K :=
  aeval ![X 0-C a*X 1+C (a*c-b)*X 2, X 1-C c*X 2, X 2]
def unchangeHom (a b c : K) : MvPolynomial (Fin 3) K →ₐ[K] MvPolynomial (Fin 3) K :=
  aeval ![X 0+C a*X 1+C b*X 2, X 1+C c*X 2, X 2]

lemma unchange_change (a b c : K) (F : MvPolynomial (Fin 3) K) :
    unchangeHom a b c (changeHom a b c F) = F := by
  induction F using MvPolynomial.induction_on with
  | C r => simp [changeHom,unchangeHom]
  | add f g hf hg => simp only [map_add,hf,hg]
  | mul_X f i hf =>
    simp only [map_mul,hf]
    congr 1
    fin_cases i <;> simp [changeHom,unchangeHom] ; ring
lemma change_unchange (a b c : K) (F : MvPolynomial (Fin 3) K) :
    changeHom a b c (unchangeHom a b c F) = F := by
  induction F using MvPolynomial.induction_on with
  | C r => simp [changeHom,unchangeHom]
  | add f g hf hg => simp only [map_add,hf,hg]
  | mul_X f i hf =>
    simp only [map_mul,hf]
    congr 1
    fin_cases i <;> simp [changeHom,unchangeHom] ; ring

def change (a b c : K) : MvPolynomial (Fin 3) K ≃ₐ[K] MvPolynomial (Fin 3) K :=
  AlgEquiv.ofAlgHom (changeHom a b c) (unchangeHom a b c)
    (AlgHom.ext (change_unchange a b c))
    (AlgHom.ext (unchange_change a b c))

lemma totalDegree_aeval_linear {σ τ : Type*} (x : τ → MvPolynomial σ K)
    (hx : ∀ i, (x i).totalDegree ≤ 1) (F : MvPolynomial τ K) :
    (MvPolynomial.aeval x F).totalDegree ≤ F.totalDegree := by
  classical
  conv_lhs => rw [F.as_sum]
  rw [map_sum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro d hd
  rw [MvPolynomial.aeval_monomial]
  apply le_trans (MvPolynomial.totalDegree_mul _ _)
  simp only [MvPolynomial.algebraMap_eq, MvPolynomial.totalDegree_C,zero_add]
  calc
    _ ≤ ∑ i ∈ d.support, (x i ^ d i).totalDegree := MvPolynomial.totalDegree_finsetProd _ _
    _ ≤ ∑ i ∈ d.support, d i := by
      apply Finset.sum_le_sum
      intro i hi
      apply (MvPolynomial.totalDegree_pow _ _).trans
      simpa [Nat.mul_comm] using Nat.mul_le_mul_right (d i) (hx i)
    _ ≤ F.totalDegree := MvPolynomial.le_totalDegree hd

lemma change_degree (a b c : K) (F : MvPolynomial (Fin 3) K) :
    (change a b c F).totalDegree ≤ F.totalDegree := by
  apply totalDegree_aeval_linear
  intro i
  fin_cases i
  · apply (totalDegree_add _ _).trans
    apply max_le
    · apply (totalDegree_sub _ _).trans
      apply max_le (by simp)
      exact (totalDegree_mul _ _).trans (by simp only [totalDegree_C,totalDegree_X]; omega)
    · exact (totalDegree_mul _ _).trans (by simp only [totalDegree_C,totalDegree_X]; omega)
  · apply (totalDegree_sub _ _).trans
    apply max_le (by simp)
    exact (totalDegree_mul _ _).trans (by simp only [totalDegree_C,totalDegree_X]; omega)
  · simp

lemma eval_change (a b c : K) (w : Fin 3 → K) (F : MvPolynomial (Fin 3) K) :
    eval w (change a b c F) =
      eval ![w 0-a*w 1+(a*c-b)*w 2,w 1-c*w 2,w 2] F := by
  change eval w (changeHom a b c F) = _
  induction F using MvPolynomial.induction_on with
  | C r => simp [changeHom]
  | add f g hf hg => simp only [map_add,hf,hg]
  | mul_X f i hf =>
    simp only [map_mul,hf]
    congr 1
    fin_cases i <;> simp [changeHom]

lemma eval_encode (y z : Polynomial K) (r : K) (F : MvPolynomial (Fin 3) K) :
    (((encode F).map (Polynomial.evalRingHom y)).eval z).eval r =
      eval ![r,y.eval r,z.eval r] F := by
  induction F using MvPolynomial.induction_on with
  | C a => simp
  | add f g hf hg => simp only [map_add,Polynomial.map_add,Polynomial.eval_add,hf,hg]
  | mul_X f i hf =>
    simp only [map_mul,Polynomial.map_mul,Polynomial.eval_mul,hf]
    congr 1
    fin_cases i <;> simp

end
end SharpLogRamsey.PolynomialCoordinates

end

namespace SharpLogRamsey.CommonLines
open GenericCoordinates PolynomialCoordinates
variable {K : Type*} [Field K] [Infinite K]
noncomputable section

lemma coprime_equiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) {F G : R} (h : IsRelPrime F G) : IsRelPrime (e F) (e G) := by
  intro a haf hag
  have hu := h (by simpa using map_dvd e.symm haf) (by simpa using map_dvd e.symm hag)
  simpa using hu.map e
omit [Infinite K] in

lemma eval_change_shear (a b c : K) (w : Fin 3 → K) (F : MvPolynomial (Fin 3) K) :
    MvPolynomial.eval (shear a b c w) (change a b c F) = MvPolynomial.eval w F := by
  rw [eval_change]
  apply congrArg (fun z : Fin 3 → K => MvPolynomial.eval z F)
  ext i
  fin_cases i <;> simp [shear] ; ring

lemma graph_zero (a b c : K) (x v : Fin 3 → K) (hv : first a b v ≠ 0)
    (F : MvPolynomial (Fin 3) K) (hF : ∀ r : K, MvPolynomial.eval (x+r • v) F = 0) :
    let U := direction (first a b) v
    let B := base (first a b) x v
    let Y := Polynomial.C ((shear a b c B) 1)+Polynomial.C ((shear a b c U) 1)*Polynomial.X
    let Z := Polynomial.C ((shear a b c B) 2)+Polynomial.C ((shear a b c U) 2)*Polynomial.X
    ((encode (change a b c F)).map (Polynomial.evalRingHom Y)).eval Z = 0 := by
  dsimp only
  apply Polynomial.funext
  intro r
  rw [Polynomial.eval_zero,eval_encode]
  let U := direction (first a b) v
  let B := base (first a b) x v
  have h0 : (shear a b c (B+r • U)) 0 = r := by
    change first a b (B+r • U) = r
    rw [map_add,map_smul,map_base _ _ _ hv,map_direction _ _ hv]
    simp
  have he : ![r,
      (Polynomial.C ((shear a b c B) 1)+Polynomial.C ((shear a b c U) 1)*Polynomial.X).eval r,
      (Polynomial.C ((shear a b c B) 2)+Polynomial.C ((shear a b c U) 2)*Polynomial.X).eval r] =
      shear a b c (B+r • U) := by
    ext i
    fin_cases i
    · exact h0.symm
    · change (Polynomial.C ((shear a b c B) 1)+Polynomial.C ((shear a b c U) 1)*Polynomial.X).eval r =
        (shear a b c (B+r • U)) 1
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
        map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
    · change (Polynomial.C ((shear a b c B) 2)+Polynomial.C ((shear a b c U) 2)*Polynomial.X).eval r =
        (shear a b c (B+r • U)) 2
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
        map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
  rw [he,eval_change_shear]
  have hp : B+r • U ∈ line x v := by
    rw [← line_normalize (first a b) x v hv]
    exact ⟨r,rfl⟩
  obtain ⟨s,hs⟩ := hp
  rw [← hs]
  exact hF s

theorem card_le {ι : Type*} [Fintype ι]
    (F G : MvPolynomial (Fin 3) K) (hc : IsRelPrime F G)
    (x v : ι → Fin 3 → K) (hv : ∀ i, v i ≠ 0)
    (hd : Function.Injective (fun i => line (x i) (v i)))
    (hF : ∀ i (r : K), MvPolynomial.eval (x i+r • v i) F = 0)
    (hG : ∀ i (r : K), MvPolynomial.eval (x i+r • v i) G = 0) :
    Fintype.card ι ≤ 2*F.totalDegree*G.totalDegree := by
  classical
  obtain ⟨a,b,c,ht,hsep⟩ := exists_separating_coordinates x v hv hd
  let Y := fun i => Polynomial.C ((shear a b c (base (first a b) (x i) (v i))) 1)+
    Polynomial.C ((shear a b c (direction (first a b) (v i))) 1)*Polynomial.X
  let Z := fun i => Polynomial.C ((shear a b c (base (first a b) (x i) (v i))) 2)+
    Polynomial.C ((shear a b c (direction (first a b) (v i))) 2)*Polynomial.X
  let e : MvPolynomial (Fin 3) K ≃ₐ[K] Polynomial (Polynomial (Polynomial K)) :=
    (change a b c).trans (encode (K := K))
  let S := Finset.univ.image (fun i => (Y i,Z i))
  have hpair : Function.Injective (fun i => (Y i,Z i)) := by
    intro i j H
    exact hsep (congrArg Prod.fst H)
  have hcard : S.card = Fintype.card ι := by simp [S,Finset.card_image_of_injective _ hpair]
  rw [← hcard]
  apply ParametricBezout.graph_branches_card_le (e F) (e G) F.totalDegree G.totalDegree
  · exact coprime_equiv (S := Polynomial (Polynomial (Polynomial K))) e.toRingEquiv hc
  · intro i
    exact (encode_coeff_natDegree (change a b c F) i).trans (change_degree a b c F)
  · intro i
    exact (encode_coeff_natDegree (change a b c G) i).trans (change_degree a b c G)
  · exact (encode_natDegree (change a b c F)).trans (change_degree a b c F)
  · exact (encode_natDegree (change a b c G)).trans (change_degree a b c G)
  · intro y hy z hz H
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hz
    exact congrArg (fun i => (Y i,Z i)) (hsep H)
  · intro z hz
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
    exact ⟨graph_zero a b c (x i) (v i) (ht i) F (hF i),
      graph_zero a b c (x i) (v i) (ht i) G (hG i)⟩

end
end SharpLogRamsey.CommonLines

end

section

namespace SharpLogRamsey.AffineIncidence
open Finset
open scoped BigOperators
variable {K : Type*} [Field K] {ι : Type*} [Fintype ι]
noncomputable section

def carrier (x v : Fin 3 → K) : Set (Fin 3 → K) := Set.range (fun r : K => x+r • v)

lemma parametrization_injective (x v : Fin 3 → K) (hv : v ≠ 0) :
    Function.Injective (fun r : K => x+r • v) := by
  intro a b H
  exact (smul_left_injective K hv) (add_left_cancel H)

lemma rebase (x v y : Fin 3 → K) (hy : y ∈ carrier x v) :
    carrier y v = carrier x v := by
  obtain ⟨s,rfl⟩ := hy
  ext z
  constructor
  · rintro ⟨r,rfl⟩
    refine ⟨s+r,?_⟩
    simp only [add_smul]
    abel
  · rintro ⟨r,rfl⟩
    refine ⟨r-s,?_⟩
    simp only [sub_smul]
    abel

lemma scale (x v : Fin 3 → K) (a : K) (ha : a ≠ 0) :
    carrier x (a • v) = carrier x v := by
  ext z
  constructor
  · rintro ⟨r,rfl⟩
    exact ⟨r*a,by simp [mul_smul]⟩
  · rintro ⟨r,rfl⟩
    exact ⟨r/a,by simp [smul_smul,ha]⟩
omit [Fintype ι] in

lemma independent_at_intersection (x v : ι → Fin 3 → K)
    (hv : ∀ i, v i ≠ 0) (hd : Function.Injective (fun i => carrier (x i) (v i)))
    (i j : ι) (hij : i ≠ j) (y : Fin 3 → K)
    (hi : y ∈ carrier (x i) (v i)) (hj : y ∈ carrier (x j) (v j)) :
    LinearIndependent K ![v i,v j] := by
  rw [linearIndependent_fin2]
  refine ⟨hv j,?_⟩
  intro a ha
  have ha0 : a ≠ 0 := by intro h; subst a; simp only [zero_smul] at ha; exact hv i ha.symm
  apply hij
  apply hd
  change carrier (x i) (v i) = carrier (x j) (v j)
  change a • v j = v i at ha
  rw [← rebase (x i) (v i) y hi,← rebase (x j) (v j) y hj,← ha,scale y (v j) a ha0]
omit [Fintype ι] in

lemma intersection_subsingleton (x v : ι → Fin 3 → K)
    (hv : ∀ i, v i ≠ 0) (hd : Function.Injective (fun i => carrier (x i) (v i)))
    (i j : ι) (hij : i ≠ j) :
    (carrier (x i) (v i) ∩ carrier (x j) (v j)).Subsingleton := by
  intro y hy z hz
  have hlin := independent_at_intersection x v hv hd i j hij y hy.1 hy.2
  have hzi : z ∈ carrier y (v i) := by rw [rebase (x i) (v i) y hy.1]; exact hz.1
  have hzj : z ∈ carrier y (v j) := by rw [rebase (x j) (v j) y hy.2]; exact hz.2
  obtain ⟨a,ha⟩ := hzi
  obtain ⟨b,hb⟩ := hzj
  have he : a • v i = b • v j := add_left_cancel (ha.trans hb.symm)
  have hc := hlin.eq_coords_of_eq (f := ![a,0]) (g := ![0,b])
    (by simpa using he) 0
  have ha0 : a = 0 := hc
  simpa [ha0] using ha
omit [Fintype ι] in

lemma points_intersection_le [DecidableEq K] (x v : ι → Fin 3 → K)
    (hv : ∀ i, v i ≠ 0) (hd : Function.Injective (fun i => carrier (x i) (v i)))
    (A : ι → Finset (Fin 3 → K)) (hA : ∀ i, (A i : Set _) ⊆ carrier (x i) (v i))
    (i j : ι) (hij : i ≠ j) : (A i ∩ A j).card ≤ 1 := by
  apply card_le_one.mpr
  intro y hy z hz
  exact intersection_subsingleton x v hv hd i j hij
    ⟨hA i (mem_inter.mp hy).1,hA j (mem_inter.mp hy).2⟩
    ⟨hA i (mem_inter.mp hz).1,hA j (mem_inter.mp hz).2⟩

variable (x v : ι → Fin 3 → K)
def pencil (y : Fin 3 → K) : Finset ι := by
  classical
  exact univ.filter (fun i => y ∈ carrier (x i) (v i))
def onLine (S : Finset (Fin 3 → K)) (i : ι) : Finset (Fin 3 → K) := by
  classical
  exact S.filter (fun y => y ∈ carrier (x i) (v i))
def richPoints (S : Finset (Fin 3 → K)) (i : ι) : Finset (Fin 3 → K) := by
  classical
  exact (onLine x v S i).filter (fun y => 2 < (pencil x v y).card)
def poorPoints (S : Finset (Fin 3 → K)) (i : ι) : Finset (Fin 3 → K) := by
  classical
  exact (onLine x v S i).filter (fun y => (pencil x v y).card ≤ 2)

lemma split_points (S : Finset (Fin 3 → K)) (i : ι) :
    (richPoints x v S i).card+(poorPoints x v S i).card = (onLine x v S i).card := by
  classical
  simpa [richPoints,poorPoints,not_lt] using
    card_filter_add_card_filter_not (s := onLine x v S i) (p := fun y => 2 < (pencil x v y).card)

lemma poor_total (S : Finset (Fin 3 → K)) :
    (∑ i, (poorPoints x v S i).card) ≤ 2*S.card := by
  classical
  have he : (∑ i, (poorPoints x v S i).card) =
      ∑ y ∈ S, if (pencil x v y).card ≤ 2 then (pencil x v y).card else 0 := by
    simp only [poorPoints,onLine,filter_filter]
    simp only [card_filter]
    rw [sum_comm]
    apply sum_congr rfl
    intro y hy
    by_cases H : (pencil x v y).card ≤ 2
    · simp only [H,and_true,ite_true]
      rw [show (pencil x v y).card = ∑ i, if y ∈ carrier (x i) (v i) then 1 else 0 by
        simp only [pencil,card_filter]]
    · simp only [H,and_false,ite_false,sum_const_zero]
  rw [he]
  calc
    _ ≤ ∑ _y ∈ S, 2 := by
      apply sum_le_sum
      intro y hy
      split_ifs with H
      · exact H
      · omega
    _ = 2*S.card := by simp [Nat.mul_comm]

theorem pruning_bound (S : Finset (Fin 3 → K)) (M D : ℕ)
    (hM : ∀ i, M ≤ (onLine x v S i).card) :
    let bad := Finset.univ.filter (fun i => (richPoints x v S i).card ≤ D)
    bad.card*(M-D) ≤ 2*S.card := by
  classical
  dsimp only
  calc
    _ = ∑ i ∈ univ.filter (fun i => (richPoints x v S i).card ≤ D), (M-D) := by simp
    _ ≤ ∑ i ∈ univ.filter (fun i => (richPoints x v S i).card ≤ D), (poorPoints x v S i).card := by
      apply sum_le_sum
      intro i hi
      have h := (mem_filter.mp hi).2
      have hs := split_points x v S i
      have hm := hM i
      omega
    _ ≤ ∑ i, (poorPoints x v S i).card := sum_le_sum_of_subset (filter_subset _ _)
    _ ≤ 2*S.card := poor_total x v S

end
end SharpLogRamsey.AffineIncidence

end

namespace SharpLogRamsey.NonplaneRichLines
open Finset MvPolynomial
open AffineIncidence
variable {K : Type*} [Field K] [Infinite K]
noncomputable section
omit [Infinite K] in

lemma eval_of_restrict_zero (x v : Fin 3 → K) (F : MvPolynomial (Fin 3) K)
    (h : LineFlatness.restrictLine x v F = 0) (y : Fin 3 → K)
    (hy : y ∈ carrier x v) : eval y F = 0 := by
  obtain ⟨t,rfl⟩ := hy
  have H := congrArg (fun p : Polynomial K => p.eval t) h
  rw [RichLinePolynomial.restriction_eval] at H
  have he : (fun i => x i+v i*t) = x+t • v := by ext i; simp [mul_comm]
  simpa only [he,Polynomial.eval_zero] using H

lemma restrict_zero_rebase (x v y : Fin 3 → K) (F : MvPolynomial (Fin 3) K)
    (h : LineFlatness.restrictLine x v F = 0) (hy : y ∈ carrier x v) :
    LineFlatness.restrictLine y v F = 0 := by
  apply Polynomial.funext
  intro r
  rw [RichLinePolynomial.restriction_eval,Polynomial.eval_zero]
  apply eval_of_restrict_zero x v F h
  rw [← rebase x v y hy]
  exact ⟨r,by ext i; simp [mul_comm]⟩

variable {ι : Type*} [Fintype ι]

lemma three_lines_at_rich (F : MvPolynomial (Fin 3) K)
    (x v : ι → Fin 3 → K) (hv : ∀ i, v i ≠ 0)
    (hd : Function.Injective (fun i => carrier (x i) (v i)))
    (hF : ∀ i, LineFlatness.restrictLine (x i) (v i) F = 0)
    (y : Fin 3 → K) (hy : 2 < (pencil x v y).card) :
    ∃ w : Fin 3 → Fin 3 → K,
      (∀ i, LineFlatness.restrictLine y (w i) F = 0) ∧
      LinearIndependent K ![w 0,w 1] ∧ LinearIndependent K ![w 0,w 2] ∧
      LinearIndependent K ![w 1,w 2] := by
  classical
  obtain ⟨a,b,c,ha,hb,hc,hab,hac,hbc⟩ := two_lt_card_iff.mp hy
  have ha' : y ∈ carrier (x a) (v a) := (mem_filter.mp ha).2
  have hb' : y ∈ carrier (x b) (v b) := (mem_filter.mp hb).2
  have hc' : y ∈ carrier (x c) (v c) := (mem_filter.mp hc).2
  refine ⟨![v a,v b,v c],?_,?_,?_,?_⟩
  · intro i
    fin_cases i
    · exact restrict_zero_rebase (x a) (v a) y F (hF a) ha'
    · exact restrict_zero_rebase (x b) (v b) y F (hF b) hb'
    · exact restrict_zero_rebase (x c) (v c) y F (hF c) hc'
  · exact independent_at_intersection x v hv hd a b hab y ha' hb'
  · exact independent_at_intersection x v hv hd a c hac y ha' hc'
  · exact independent_at_intersection x v hv hd b c hbc y hb' hc'
omit [Infinite K] in

lemma many_parameters (x v : ι → Fin 3 → K) (hv : ∀ i, v i ≠ 0)
    (S : Finset (Fin 3 → K)) (i : ι) :
    ∃ T : Finset K, T.card = (richPoints x v S i).card ∧
      ∀ t ∈ T, 2 < (pencil x v (fun j => x i j+v i j*t)).card := by
  classical
  let f : K → Fin 3 → K := fun t => x i+t • v i
  let T := (richPoints x v S i).preimage f (parametrization_injective _ _ (hv i)).injOn
  refine ⟨T,?_,?_⟩
  · rw [card_preimage]
    congr 1
    apply filter_eq_self.mpr
    intro y hy
    exact (mem_filter.mp (mem_filter.mp hy).1).2
  · intro t ht
    have H := (mem_filter.mp (mem_preimage.mp ht)).2
    have he : f t = (fun j => x i j+v i j*t) := by ext j; simp [f,mul_comm]
    simpa only [he] using H

end
end SharpLogRamsey.NonplaneRichLines
end
end

end OAI
