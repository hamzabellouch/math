import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.TracialCohomology.Homogeneous
import OAI.Analysis.TracialCohomology.MatrixRepresentations

namespace OAI

/-! Central matrices for bounded Hochschild cohomology. -/

noncomputable section

open Filter Topology
open scoped ComplexOrder
namespace PopaCenter
open PopaMatrices PopaCorners.CornerIso PopaPatching
open BoundedHochschild HochschildRigidity HochschildDiffuse PopaTypeII
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)

include h1 in
theorem homogeneous_partition (hII : PopaTypeII.NoAbelianCorners M) (n : ℕ)
    {p : M} (hp : IsStarProjection p) (hEp : Homogeneous e τ hτ htr hfaith p) (t : ℝ) (ht : 0 ≤ t)
    (hnt : (n : ℝ)*t=(τ p).re) :
    ∃ q : Fin n → M, (∀ i, IsStarProjection (q i)) ∧
      (∀ i, q i ≤ p) ∧ (∀ i, (τ (q i)).re=t) ∧ (∀ i, Homogeneous e τ hτ htr hfaith (q i)) ∧
      (∀ i j, i ≠ j → q i*q j=0) ∧ ∑ i, q i=p := by
  induction n generalizing p with
  | zero =>
    have hp0 : p=0 := by
      by_contra hn
      have hpos := projection_trace_pos τ hfaith hp hn
      simp only [Nat.cast_zero,zero_mul] at hnt
      linarith
    refine ⟨Fin.elim0,fun i => Fin.elim0 i,fun i => Fin.elim0 i,
      fun i => Fin.elim0 i,fun i => Fin.elim0 i,fun i => Fin.elim0 i,?_⟩
    simp [hp0]
  | succ n ih =>
    have htp : t ≤ (τ p).re := by
      rw [← hnt,Nat.cast_succ,add_mul,one_mul]
      exact le_add_of_nonneg_left (mul_nonneg (Nat.cast_nonneg n) ht)
    obtain ⟨a,ha,hap,hat,haE⟩ := exists_homogeneous_trace e τ hτ htr hfaith h1 hII hp hEp t ht htp
    have hpa : IsStarProjection (p-a) := (ha.le_iff_sub hp).mp hap
    have hrem : (n : ℝ)*t=(τ (p-a)).re := by
      rw [map_sub,Complex.sub_re,hat,← hnt,Nat.cast_succ]
      ring
    obtain ⟨q,hq,hqp,hqt,hqE,hqo,hqs⟩ := ih hpa (homogeneous_sub e τ hτ htr hfaith h1 hEp haE) hrem
    refine ⟨Fin.cons a q,?_,?_,?_,?_,?_,?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact ha
      · exact hq j
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact hap
      · exact (hqp j).trans (sub_le_self _ ha.nonneg)
    · intro i
      exact Fin.cases hat hqt i
    · intro i; exact Fin.cases haE hqE i
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i <;> intro j <;>
        refine Fin.cases ?_ (fun j => ?_) j <;> intro hij
      · exact False.elim (hij rfl)
      · exact orthogonal_of_le_complement hp ha (hq j) hap (hqp j)
      · have he := congrArg star (orthogonal_of_le_complement hp ha (hq i) hap (hqp i))
        simpa only [Fin.cons_succ,Fin.cons_zero,star_mul,ha.isSelfAdjoint.star_eq,
          (hq i).isSelfAdjoint.star_eq,star_zero] using he
      · exact hqo i j (fun h => hij (congrArg Fin.succ h))
    · rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero,Fin.cons_succ,hqs]
      abel

include h1 in
lemma system_of_partition {n : ℕ} {p : M} (hn : 0 < n) (q : Fin n → M)
    (hq : ∀ i, IsStarProjection (q i)) (hqt : ∀ i j, average e τ hτ htr hfaith (q i)=average e τ hτ htr hfaith (q j))
    (hqo : ∀ i j, i ≠ j → q i*q j=0) (hqs : ∑ i, q i=p) :
    ∃ s : System n p, ∀ i, s.entry i i=q i := by
  let i0 : Fin n := ⟨0,hn⟩
  have hex (i : Fin n) : ∃ v : M, star v*v=q i0 ∧ v*star v=q i ∧
      v*q i0=v ∧ q i*v=v := equivalent_of_average_eq e τ hτ htr hfaith
        h1 (hq i0) (hq i) (hqt i0 i)
  choose v hvi hvf hvr hlv using hex
  have hov (i j : Fin n) (hij : i ≠ j) : star (v i)*v j=0 := by
    have hstar : star (v i)*q i=star (v i) := by
      simpa only [star_mul,(hq i).isSelfAdjoint.star_eq] using congrArg star (hlv i)
    calc
      star (v i)*v j=star (v i)*(q i*(q j*v j)) := by rw [hlv,← mul_assoc,hstar]
      _ = 0 := by rw [← mul_assoc (q i),hqo i j hij,zero_mul,mul_zero]
  let s : System n p := {
    entry := fun i j => v i*star (v j)
    star_entry := fun i j => by simp only [star_mul,star_star]
    mul_entry := fun i j k l => by
      by_cases h : j=k
      · subst k
        simp only
        calc
          (v i*star (v j))*(v j*star (v l)) = (v i*(star (v j)*v j))*star (v l) := by
            simp only [mul_assoc]
          _ = v i*star (v l) := by rw [hvi,hvr]
      · simp only [ite_eq_right h]
        calc
          (v i*star (v j))*(v k*star (v l)) = (v i*(star (v j)*v k))*star (v l) := by
            simp only [mul_assoc]
          _ = 0 := by rw [hov j k h,mul_zero,zero_mul]
    sum_diag := by simpa only [hvf] using hqs }
  exact ⟨s,hvf⟩

include h1 in
theorem exists_homogeneous_system (hII : PopaTypeII.NoAbelianCorners M) (n : ℕ) (hn : 0<n)
    {p : M} (hp : IsStarProjection p) (hEp : Homogeneous e τ hτ htr hfaith p) :
    Nonempty (System n p) := by
  have hn0 : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hpn : 0 ≤ (τ p).re := (Complex.nonneg_iff.mp (τ.map_nonneg hp.nonneg)).1
  obtain ⟨q,hq,hqp,hqt,hqE,hqo,hqs⟩ := homogeneous_partition e τ hτ htr hfaith h1 hII n hp hEp
    ((τ p).re/n) (div_nonneg hpn (Nat.cast_nonneg n)) (by field_simp)
  obtain ⟨s,hs⟩ := system_of_partition e τ hτ htr hfaith h1 hn q hq (fun i j => by
    rw [show average e τ hτ htr hfaith (q i)=(τ (q i)).re • (1:M) from hqE i,
      show average e τ hτ htr hfaith (q j)=(τ (q j)).re • (1:M) from hqE j,hqt,hqt]) hqo hqs
  exact ⟨s⟩

include h1 in
lemma off_diagonal_average {n : ℕ} {p : M} (s : System n p)
    {i j : Fin n} (hij : i ≠ j) : average e τ hτ htr hfaith (s.entry i j)=0 := by
  have hh := average_trace e τ hτ htr hfaith h1 (s.entry i i) (s.entry i j)
  simp only [s.mul_entry,ite_eq_right (Ne.symm hij)] at hh
  change average e τ hτ htr hfaith (s.entry i j)=average e τ hτ htr hfaith 0 at hh
  have hz : average e τ hτ htr hfaith (0:M)=0 := map_zero (expectation e τ hτ htr hfaith h1)
  exact hh.trans hz

include h1 in
theorem finite_corner_rep {A : Type*} (hII : PopaTypeII.NoAbelianCorners M)
    {p : M} (hp : IsStarProjection p) (hEp : Homogeneous e τ hτ htr hfaith p) (S : Finset (FreeGroup A)) :
    ∃ w : Rep (FreeGroup A) M, w.support=p ∧
      ∀ g ∈ S, g ≠ 1 → average e τ hτ htr hfaith (w g)=0 := by
  classical
  obtain ⟨H,hG,hF,π,hπ⟩ := PopaFinite.exists_finite_separation S
  let := hG
  let := hF
  obtain ⟨s⟩ := exists_homogeneous_system e τ hτ htr hfaith h1 hII (Fintype.card H) Fintype.card_pos hp hEp
  refine ⟨matrixRep s (regularPerm π),matrixRep_support s _,fun g hg hg1 => ?_⟩
  change expectation e τ hτ htr hfaith h1 (∑ i, s.entry (regularPerm π g i) i)=0
  rw [map_sum]
  exact Finset.sum_eq_zero (fun i _ => off_diagonal_average e τ hτ htr hfaith h1 s (regularPerm_ne π g (hπ g hg hg1) i))
end PopaCenter

open scoped ComplexOrder
namespace PopaTypeII
open PopaCorners PopaCorners.CornerIso
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

omit [PartialOrder M] [StarOrderedRing M] in
lemma square_zero_noncommute {a : M} (ha : a*a=0) (ha0 : a ≠ 0) : ¬ Commute a (star a) := by
  intro hc
  have hh : (star a*a)*(star a*a)=0 := by
    calc
      _=star a*(a*star a)*a := by simp only [mul_assoc]
      _=star a*(star a*a)*a := by rw [hc.eq]
      _=(star a*star a)*(a*a) := by simp only [mul_assoc]
      _=0 := by rw [ha,mul_zero]
  have hn := (IsSelfAdjoint.star_mul_self a).norm_mul_self
  rw [hh,norm_zero] at hn
  have hz : star a*a=0 := norm_eq_zero.mp (by nlinarith [norm_nonneg (star a*a)])
  have hra := CStarRing.norm_star_mul_self (x:=a)
  rw [hz,norm_zero] at hra
  exact ha0 (norm_eq_zero.mp (by nlinarith [norm_nonneg a]))

omit [PartialOrder M] [StarOrderedRing M] in
lemma corner_noncommutative_of_nilpotent {p : M} (hp : IsStarProjection p) {a : M}
    (hpa : p*a=a) (hap : a*p=a) (ha : a*a=0) (ha0 : a ≠ 0) :
    ∃ x y : PopaCorner.algebra hp, ¬ Commute x y := by
  let x : PopaCorner.algebra hp := ⟨a,hpa,hap⟩
  refine ⟨x,star x,fun hc => square_zero_noncommute ha ha0 ?_⟩
  exact congrArg Subtype.val hc.eq

lemma corner_transfer_nilpotent {p q : M} (hp : IsStarProjection p)
    (v : CornerIso q p) (hv : v.initial=q) {a : M}
    (hqa : q*a=a) (haq : a*q=a) (ha : a*a=0) (ha0 : a ≠ 0) :
    ∃ x y : PopaCorner.algebra hp, ¬ Commute x y := by
  have hpv : p*(v:M)=(v:M) := by
    calc
      _=p*(v.final*(v:M)) := by rw [v.final_mul]
      _=(p*v.final)*(v:M) := by rw [mul_assoc]
      _=v.final*(v:M) := by rw [(v.final_proj.le_iff_mul_eq_right hp).mp v.final_le]
      _=(v:M) := v.final_mul
  have hvp : star (v:M)*p=star (v:M) := by
    simpa only [star_mul,hp.isSelfAdjoint.star_eq] using congrArg star hpv
  let b : M := (v:M)*a*star (v:M)
  have hpb : p*b=b := by dsimp [b]; rw [←mul_assoc,←mul_assoc,hpv]
  have hbp : b*p=b := by dsimp [b]; rw [mul_assoc,hvp]
  have hb : b*b=0 := by
    change ((v:M)*a*star (v:M))*((v:M)*a*star (v:M))=0
    calc
      _=(v:M)*(a*(star (v:M)*(v:M))*a)*star (v:M) := by simp only [mul_assoc]
      _=(v:M)*0*star (v:M) := by rw [show star (v:M)*(v:M)=q from hv,haq,ha]
      _=0 := by simp
  have hb0 : b ≠ 0 := by
    intro hz
    have hh : star (v:M)*b*(v:M)=a := by
      dsimp [b]
      calc
        _=(star (v:M)*(v:M))*a*(star (v:M)*(v:M)) := by simp only [mul_assoc]
        _=a := by rw [show star (v:M)*(v:M)=q from hv,hqa,haq]
    rw [hz,mul_zero,zero_mul] at hh
    exact ha0 hh.symm
  exact corner_noncommutative_of_nilpotent hp hpb hbp hb hb0
end PopaTypeII

open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildRigidity PopaMatrices
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)

include h1 in
lemma system_diagonal_average {n : ℕ} (hn : 0<n) (s : System n (1:M)) (i : Fin n) :
    average e τ hτ htr hfaith (s.entry i i)=(n:ℝ)⁻¹ • (1:M) := by
  have he (j : Fin n) : average e τ hτ htr hfaith (s.entry j j)=average e τ hτ htr hfaith (s.entry i i) := by
    have hh := average_trace e τ hτ htr hfaith h1 (s.entry j i) (s.entry i j)
    simpa only [s.mul_entry,ite_true] using hh
  have hs : (n:ℝ) • average e τ hτ htr hfaith (s.entry i i)=(1:M) := by
    calc
      _=∑ j, average e τ hτ htr hfaith (s.entry j j) := by
        simp only [he,Finset.sum_const,Finset.card_univ,Fintype.card_fin,Nat.cast_smul_eq_nsmul]
      _=average e τ hτ htr hfaith (1:M) := by
        change (∑ j, expectation e τ hτ htr hfaith h1 (s.entry j j))=expectation e τ hτ htr hfaith h1 1
        rw [←map_sum,s.sum_diag]
      _=1 := average_id e τ hτ htr hfaith h1 (fun x => Commute.one_left x)
  have hh := congrArg (fun b : M => (n:ℝ)⁻¹ • b) hs
  rw [smul_smul,inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)),one_smul] at hh
  exact hh

include h1 in
lemma system_cut_diagonal_average {n : ℕ} (hn : 0<n) (s : System n (1:M)) (i : Fin n)
    {z : M} (hz : Central z) :
    average e τ hτ htr hfaith (z*s.entry i i)=(n:ℝ)⁻¹ • z := by
  rw [average_bimodule e τ hτ htr hfaith h1 hz,system_diagonal_average e τ hτ htr hfaith h1 hn s i,
    mul_smul_comm,mul_one]

omit [PartialOrder M] [StarOrderedRing M] in
lemma central_projection_mul {z : M} (hz : IsStarProjection z) (hzc : Central z) (a b : M) :
    (z*a)*(z*b)=z*(a*b) := by
  calc
    _=z*(a*z)*b := by simp only [mul_assoc]
    _=z*(z*a)*b := by rw [(hzc a).eq]
    _=(z*z)*(a*b) := by simp only [mul_assoc]
    _=z*(a*b) := by rw [hz.isIdempotentElem.eq]

include h1 in

lemma nonzero_central_digit {p : M} (hp : IsStarProjection p) (hp0 : p ≠ 0) :
    ∃ k : ℕ, ∃ z : M, IsStarProjection z ∧ Central z ∧ z ≠ 0 ∧
      ((2:ℝ)^k)⁻¹ • z ≤ average e τ hτ htr hfaith p := by
  classical
  have ht : 0<(τ p).re := HochschildDiffuse.projection_trace_pos τ hfaith hp hp0
  obtain ⟨m,hm⟩ := exists_nat_gt (1/(τ p).re)
  let k := m+1
  have hmk : (m:ℝ)<(2:ℝ)^k := by exact_mod_cast (Nat.lt_succ_self m).trans Nat.lt_two_pow_self
  have hbig : 1<(2:ℝ)^k*(τ p).re := (div_lt_iff₀ ht).mp (hm.trans hmk)
  have ha0 := average_nonneg e τ hτ htr hfaith hp.nonneg
  have ha1 : average e τ hτ htr hfaith p≤1 := by
    simpa only [average_id e τ hτ htr hfaith h1 (fun x => Commute.one_left x)] using
      average_mono e τ hτ htr hfaith h1 hp.le_one
  obtain ⟨z,hz,hzc,hlo,hhi⟩ := central_dyadic_digits e k (average e τ hτ htr hfaith p)
    ha0 ha1 (average_central e τ hτ htr hfaith p)
  have hex : ∃ i, z i ≠ 0 := by
    by_contra hh
    push Not at hh
    simp only [hh,Finset.sum_const_zero,sub_zero] at hhi
    have ht' := Complex.re_le_re (τ.monotone hhi)
    change (τ ((2:ℝ)^k • average e τ hτ htr hfaith p)).re≤(τ 1).re at ht'
    rw [τ.map_smul_of_tower,trace_average e τ hτ htr hfaith h1,h1] at ht'
    simp only [Complex.real_smul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,Complex.one_re] at ht'
    linarith
  obtain ⟨i,hi⟩ := hex
  have hzle : z i≤(2:ℝ)^k • average e τ hτ htr hfaith p := by
    exact (Finset.single_le_sum (fun j _ => (hz j).nonneg) (Finset.mem_univ i)).trans (sub_nonneg.mp hlo)
  refine ⟨k,z i,hz i,hzc i,hi,?_⟩
  have hh := smul_le_smul_of_nonneg_left hzle (inv_nonneg.mpr (pow_pos (by norm_num : (0:ℝ)<2) k).le)
  simpa only [smul_smul,inv_mul_cancel₀ (pow_ne_zero k (by norm_num : (2:ℝ) ≠ 0)),one_smul] using hh
end PopaCenter

open scoped ComplexOrder
namespace PopaTypeII
open BoundedHochschild PopaCenter PopaMatrices PopaCorners
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)

include e hτ htr hfaith h1 in

theorem noAbelianCorners_of_matrices
    (hmat : ∀ k : ℕ, Nonempty (System (2^(k+1)) (1:M))) : NoAbelianCorners M := by
  intro p hp hp0
  obtain ⟨k,z,hz,hzc,hz0,hzp⟩ := nonzero_central_digit e τ hτ htr hfaith h1 hp hp0
  obtain ⟨s⟩ := hmat k
  let n := 2^(k+1)
  have hn : 2≤n := by
    dsimp [n]
    calc 2=2^1 := by norm_num
         _≤2^(k+1) := Nat.pow_le_pow_right (by decide) (by omega)
  have hn0 : 0<n := by omega
  let i : Fin n := ⟨0,hn0⟩
  let j : Fin n := ⟨1,by omega⟩
  have hij : i ≠ j := by intro he; have := congrArg Fin.val he; simp [i,j] at this
  let a := z*s.entry i i
  let b := z*s.entry j j
  let u := z*s.entry i j
  have ha : IsStarProjection a := hz.mul (s.diagonal_projection i) (hzc _)
  have hb : IsStarProjection b := hz.mul (s.diagonal_projection j) (hzc _)
  have hab : a*b=0 := by
    dsimp [a,b]
    rw [central_projection_mul hz hzc,s.mul_entry,ite_eq_right hij,mul_zero]
  let q := a+b
  have hq : IsStarProjection q := ha.add hb hab
  have hqa : q*u=u := by
    dsimp [q,a,b,u]
    rw [add_mul,central_projection_mul hz hzc,central_projection_mul hz hzc,
      s.mul_entry,s.mul_entry,ite_eq_left rfl,ite_eq_right hij.symm,mul_zero,add_zero]
  have haq : u*q=u := by
    dsimp [q,a,b,u]
    rw [mul_add,central_projection_mul hz hzc,central_projection_mul hz hzc,
      s.mul_entry,s.mul_entry,ite_eq_right hij.symm,ite_eq_left rfl,mul_zero,zero_add]
  have hu : u*u=0 := by
    dsimp [u]
    rw [central_projection_mul hz hzc,s.mul_entry,ite_eq_right hij.symm,mul_zero]
  have hEq : average e τ hτ htr hfaith q=((2:ℝ)^k)⁻¹ • z := by
    change expectation e τ hτ htr hfaith h1 (a+b)=_
    rw [map_add]
    change average e τ hτ htr hfaith (z*s.entry i i)+average e τ hτ htr hfaith (z*s.entry j j)=_
    rw [system_cut_diagonal_average e τ hτ htr hfaith h1 hn0 s i hzc,
      system_cut_diagonal_average e τ hτ htr hfaith h1 hn0 s j hzc,←add_smul]
    congr 1
    dsimp [n]
    rw [Nat.cast_pow,Nat.cast_ofNat,pow_succ]
    field_simp
    ring
  have hu0 : u ≠ 0 := by
    intro hu0
    have haz : a=0 := by
      have hh : u*(z*s.entry j i)=a := by
        dsimp [u,a]
        rw [central_projection_mul hz hzc,s.mul_entry,ite_eq_left rfl]
      rw [hu0,zero_mul] at hh
      exact hh.symm
    have hEa := system_cut_diagonal_average e τ hτ htr hfaith h1 hn0 s i hzc
    change average e τ hτ htr hfaith a=(n:ℝ)⁻¹ • z at hEa
    rw [haz,show average e τ hτ htr hfaith (0:M)=0 from map_zero (expectation e τ hτ htr hfaith h1)] at hEa
    exact hz0 ((smul_eq_zero.mp hEa.symm).resolve_left (inv_ne_zero (Nat.cast_ne_zero.mpr hn0.ne')))
  obtain ⟨v,hv⟩ := exists_full_initial_of_average_le e τ hτ htr hfaith h1 hq hp (by rwa [hEq])
  exact corner_transfer_nilpotent hp v hv hqa haq hu hu0
end PopaTypeII

end

end OAI
