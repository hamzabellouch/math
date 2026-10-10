import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.TracialCohomology.TypeII
import OAI.Analysis.TracialCohomology.CenterTrace
import OAI.Analysis.TracialCohomology.Expectations

namespace OAI

/-! Partitions for bounded Hochschild cohomology. -/

noncomputable section

open scoped ComplexOrder
namespace PopaMatrices
open BoundedHochschild HochschildRigidity HochschildDiffuse PopaCorners
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
  (h1 : τ 1=1)
  (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1:M))

include e hτ htr hfaith h1 hfactor in
lemma system_of_partition {n : ℕ} (hn : 0 < n) (q : Fin n → M)
    (hq : ∀ i, IsStarProjection (q i)) (hqt : ∀ i j, (τ (q i)).re=(τ (q j)).re)
    (hqo : ∀ i j, i ≠ j → q i*q j=0) (hqs : ∑ i, q i=1) :
    ∃ s : System n (1:M), ∀ i, s.entry i i=q i := by
  let i0 : Fin n := ⟨0,hn⟩
  have hex (i : Fin n) : ∃ v : M, star v*v=q i0 ∧ v*star v=q i ∧
      v*q i0=v ∧ q i*v=v := CornerIso.equivalent_of_trace_eq e τ hτ htr hfaith
        h1 hfactor (hq i0) (hq i) (hqt i0 i)
  choose v hvi hvf hvr hlv using hex
  have hov (i j : Fin n) (hij : i ≠ j) : star (v i)*v j=0 := by
    have hstar : star (v i)*q i=star (v i) := by
      simpa only [star_mul,(hq i).isSelfAdjoint.star_eq] using congrArg star (hlv i)
    calc
      star (v i)*v j=star (v i)*(q i*(q j*v j)) := by rw [hlv,← mul_assoc,hstar]
      _ = 0 := by rw [← mul_assoc (q i),hqo i j hij,zero_mul,mul_zero]
  let s : System n (1:M) := {
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

lemma orthogonal_of_complement {p a b : M} (hp : IsStarProjection p)
    (ha : IsStarProjection a) (hb : IsStarProjection b) (hap : a ≤ p) (hbp : b ≤ 1-p) :
    a*b=0 := by
  have hpb := orthogonal_of_le_complement (IsStarProjection.one M) hp hb hp.le_one hbp
  calc
    a*b=(a*p)*b := by rw [(ha.le_iff_mul_eq_left hp).mp hap]
    _ = 0 := by rw [mul_assoc,hpb,mul_zero]

include e hτ htr hfaith h1 hfactor in

lemma system_containing_rational_projection (hdiff : NoMinimalProjections M)
    (k l : ℕ) (hn : 0 < k+l) {p : M} (hp : IsStarProjection p)
    (hpt : (τ p).re=(k:ℝ)/(k+l:ℕ)) :
    ∃ s : System (k+l) (1:M), ∀ x : M, Commute (s.expect x) p := by
  have hn0 : ((k+l:ℕ):ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have htn : 0 ≤ (((k+l:ℕ):ℝ)⁻¹) := inv_nonneg.mpr (Nat.cast_nonneg _)
  obtain ⟨a,ha,hap,hat,hao,has⟩ := equal_partition e τ hτ htr hfaith hdiff k hp
    (((k+l:ℕ):ℝ)⁻¹) htn (by rw [hpt,div_eq_mul_inv])
  have hpc : IsStarProjection (1-p) := (hp.le_iff_sub (IsStarProjection.one M)).mp hp.le_one
  have hcamt : (l:ℝ)*(((k+l:ℕ):ℝ)⁻¹)=(τ (1-p)).re := by
    rw [map_sub,h1,Complex.sub_re,Complex.one_re,hpt]
    have hncast : ((k+l:ℕ):ℝ)=(k:ℝ)+(l:ℝ) := Nat.cast_add _ _
    rw [div_eq_mul_inv]
    apply (eq_sub_iff_add_eq).mpr
    rw [← add_mul,add_comm (l:ℝ),← hncast,mul_inv_cancel₀ hn0]
  obtain ⟨b,hb,hbp,hbt,hbo,hbs⟩ := equal_partition e τ hτ htr hfaith hdiff l hpc
    (((k+l:ℕ):ℝ)⁻¹) htn hcamt
  let q := Fin.append a b
  have hq (i : Fin (k+l)) : IsStarProjection (q i) := by
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · simpa [q] using ha i
    · simpa [q] using hb j
  have hqt (i : Fin (k+l)) : (τ (q i)).re=(((k+l:ℕ):ℝ)⁻¹) := by
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · simpa [q] using hat i
    · simpa [q] using hbt j
  have hqo (i j : Fin (k+l)) (hij : i ≠ j) : q i*q j=0 := by
    revert hij
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> intro hij
    · simpa [q] using hao i j (fun h => hij (congrArg (Fin.castAdd l) h))
    · simpa [q] using orthogonal_of_complement hp (ha i) (hb j) (hap i) (hbp j)
    · have he := congrArg star (orthogonal_of_complement hp (ha j) (hb i) (hap j) (hbp i))
      simpa [q,star_mul,(ha j).isSelfAdjoint.star_eq,(hb i).isSelfAdjoint.star_eq] using he
    · simpa [q] using hbo i j (fun h => hij (congrArg (Fin.natAdd k) h))
  have hqs : ∑ i, q i=1 := by
    simp only [q,Fin.sum_univ_add,Fin.append_left,Fin.append_right,has,hbs]
    abel
  obtain ⟨s,hs⟩ := system_of_partition e τ hτ htr hfaith h1 hfactor hn q hq
    (fun i j => (hqt i).trans (hqt j).symm) hqo hqs
  refine ⟨s,fun x => ?_⟩
  rw [← has]
  apply Commute.sum_right
  intro i _
  have hh := s.expect_mem x (Fin.castAdd l i) (Fin.castAdd l i)
  simpa only [hs,q,Fin.append_left] using hh
end PopaMatrices

open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildRigidity PopaCorners PopaCorners.CornerIso PopaMatrices PopaTypeII
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)

include e hτ htr hfaith h1 in
lemma system_of_central_partition {n : ℕ} (hn : 0 < n) (q : Fin n → M)
    (hq : ∀ i, IsStarProjection (q i)) (hqt : ∀ i j, average e τ hτ htr hfaith (q i)=average e τ hτ htr hfaith (q j))
    (hqo : ∀ i j, i ≠ j → q i*q j=0) (hqs : ∑ i, q i=1) :
    ∃ s : System n (1:M), ∀ i, s.entry i i=q i := by
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
  let s : System n (1:M) := {
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

lemma orthogonal_of_subprojections {p q a b : M} (hp : IsStarProjection p)
    (hq : IsStarProjection q) (ha : IsStarProjection a) (hb : IsStarProjection b)
    (hap : a ≤ p) (hbq : b ≤ q) (hpq : p*q=0) : a*b=0 := by
  calc
    _=(a*p)*(q*b) := by rw [(ha.le_iff_mul_eq_left hp).mp hap,(hb.le_iff_mul_eq_right hq).mp hbq]
    _=a*(p*q)*b := by simp only [mul_assoc]
    _=0 := by rw [hpq,mul_zero,zero_mul]

include h1 in
lemma halving_average {p : M} (v : CornerIso p p) (hv : v.initial+v.final=p) :
    average e τ hτ htr hfaith v.initial=(2:ℂ)⁻¹ • average e τ hτ htr hfaith p ∧
    average e τ hτ htr hfaith v.final=(2:ℂ)⁻¹ • average e τ hτ htr hfaith p := by
  have he : average e τ hτ htr hfaith v.initial=average e τ hτ htr hfaith v.final :=
    average_trace e τ hτ htr hfaith h1 (star (v:M)) (v:M)
  have htwo : (2:ℂ) • average e τ hτ htr hfaith v.initial=average e τ hτ htr hfaith p := by
    rw [two_smul]
    calc
      _ = average e τ hτ htr hfaith v.initial + average e τ hτ htr hfaith v.final := by rw [he]
      _ = _ := by rw [←average_add e τ hτ htr hfaith h1,hv]
  have hi : average e τ hτ htr hfaith v.initial=(2:ℂ)⁻¹ • average e τ hτ htr hfaith p := by
    rw [←htwo,smul_smul,inv_mul_cancel₀ (by norm_num : (2:ℂ)≠0),one_smul]
  exact ⟨hi,he.symm.trans hi⟩

include e hτ htr hfaith h1 in
lemma double_partition (hII : NoAbelianCorners M) {n : ℕ} {p : M}
    (q : Fin n → M) (hq : ∀ i, IsStarProjection (q i))
    (hqt : ∀ i j, average e τ hτ htr hfaith (q i)=average e τ hτ htr hfaith (q j))
    (hqo : ∀ i j, i ≠ j → q i*q j=0) (hqs : ∑ i, q i=p) :
    ∃ r : Fin (n+n) → M, (∀ i, IsStarProjection (r i)) ∧
      (∀ i j, average e τ hτ htr hfaith (r i)=average e τ hτ htr hfaith (r j)) ∧
      (∀ i j, i ≠ j → r i*r j=0) ∧ ∑ i, r i=p := by
  classical
  choose v hvo hvs using fun i => halve_projection e τ hτ htr hfaith hII (hq i)
  let a := fun i => (v i).initial
  let b := fun i => (v i).final
  have ht := fun i => halving_average e τ hτ htr hfaith h1 (v i) (hvs i)
  let r := Fin.append a b
  have hr (i : Fin (n+n)) : IsStarProjection (r i) :=
    Fin.addCases (fun j => by simpa only [r,Fin.append_left,a] using (v j).initial_proj)
      (fun j => by simpa only [r,Fin.append_right,b] using (v j).final_proj) i
  refine ⟨r,hr,?_,?_,?_⟩
  · intro i j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
      simp only [r,Fin.append_left,Fin.append_right,a,b,(ht _).1,(ht _).2,hqt i j]
  · intro i j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> intro hij <;>
      simp only [r,Fin.append_left,Fin.append_right,a,b]
    · exact orthogonal_of_subprojections (hq i) (hq j) (v i).initial_proj (v j).initial_proj
        (v i).init_le (v j).init_le (hqo i j (fun h => hij (congrArg (Fin.castAdd n) h)))
    · by_cases h : i=j
      · subst j; exact hvo i
      · exact orthogonal_of_subprojections (hq i) (hq j) (v i).initial_proj (v j).final_proj
          (v i).init_le (v j).final_le (hqo i j h)
    · by_cases h : i=j
      · subst j
        simpa only [star_mul,(v i).initial_proj.isSelfAdjoint.star_eq,
          (v i).final_proj.isSelfAdjoint.star_eq,star_zero] using congrArg star (hvo i)
      · exact orthogonal_of_subprojections (hq i) (hq j) (v i).final_proj (v j).initial_proj
          (v i).final_le (v j).init_le (hqo i j h)
    · exact orthogonal_of_subprojections (hq i) (hq j) (v i).final_proj (v j).final_proj
        (v i).final_le (v j).final_le (hqo i j (fun h => hij (congrArg (Fin.natAdd n) h)))
  · simp only [r,Fin.sum_univ_add,Fin.append_left,Fin.append_right,a,b,←Finset.sum_add_distrib,hvs,hqs]

include e hτ htr hfaith h1 in
lemma dyadic_partition (hII : NoAbelianCorners M) (k : ℕ) {p : M} (hp : IsStarProjection p) :
    ∃ q : Fin (2^k) → M, (∀ i, IsStarProjection (q i)) ∧
      (∀ i j, average e τ hτ htr hfaith (q i)=average e τ hτ htr hfaith (q j)) ∧
      (∀ i j, i ≠ j → q i*q j=0) ∧ ∑ i, q i=p := by
  induction k with
  | zero =>
    change ∃ q : Fin 1 → M, _
    refine ⟨fun _ => p,fun _ => hp,fun _ _ => rfl,?_,?_⟩
    · intro i j hij; exact (hij (Fin.ext (by have hi := i.isLt; have hj := j.isLt; norm_num at hi hj; omega))).elim
    · simp
  | succ k ih =>
    obtain ⟨q,hq,hqt,hqo,hqs⟩ := ih
    rw [pow_succ,Nat.mul_two]
    exact double_partition e τ hτ htr hfaith h1 hII q hq hqt hqo hqs

include e hτ htr hfaith h1 in
theorem exists_dyadic_system (hII : NoAbelianCorners M) (k : ℕ) :
    Nonempty (System (2^k) (1:M)) := by
  obtain ⟨q,hq,hqt,hqo,hqs⟩ := dyadic_partition e τ hτ htr hfaith h1 hII k (IsStarProjection.one M)
  obtain ⟨s,_⟩ := system_of_central_partition e τ hτ htr hfaith h1 (by positivity) q hq hqt hqo hqs
  exact ⟨s⟩
end PopaCenter

open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildRigidity HochschildSakai
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

omit [PartialOrder M] [StarOrderedRing M] in
lemma central_smul_real (r : ℝ) {a : M} (ha : Central a) : Central (r • a) := by
  intro x
  change (r • a)*x=x*(r • a)
  rw [smul_mul_assoc,mul_smul_comm,(ha x).eq]

omit [PartialOrder M] [StarOrderedRing M] in
lemma central_posPart {a : M} (ha : Central a) : Central a⁺ := by
  intro x
  exact (ha x).cfcₙ_real (fun r : ℝ => r⁺)

variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

include e in
theorem exists_central_dyadic_projection (a : M) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (ha : Central a) :
    ∃ p : M, IsStarProjection p ∧ Central p ∧ 0 ≤ (2:ℝ) • a-p ∧ (2:ℝ) • a-p ≤ 1 := by
  let b : M := a-(1/2:ℝ) • (1:M)
  let c : M := b⁺
  let d : M := b⁻
  have hbsa : IsSelfAdjoint b := (IsSelfAdjoint.of_nonneg ha0).sub
    (IsSelfAdjoint.of_nonneg (smul_nonneg (by norm_num : (0:ℝ) ≤ 1/2) zero_le_one))
  have hb : c-d=b := CFC.posPart_sub_negPart b hbsa
  have hc0 : 0 ≤ c := CFC.posPart_nonneg b
  have hd0 : 0 ≤ d := CFC.negPart_nonneg b
  obtain ⟨p,hp⟩ := exists_support_projection e c hc0
  have hpd : p*d=0 := hp.annihilate d (CFC.posPart_mul_negPart b)
  have hdp : d*p=0 := by
    simpa only [star_mul,(IsSelfAdjoint.of_nonneg hd0).star_eq,
      hp.proj.isSelfAdjoint.star_eq,star_zero] using congrArg star hpd
  have hcp : b*p=c := by rw [← hb,sub_mul,hp.right,hdp,sub_zero]
  have hpc : p*b=c := by rw [← hb,mul_sub,hp.left,hpd,sub_zero]
  have hac : Commute a p := by
    change a*p=p*a
    have hh := hcp.trans hpc.symm
    dsimp [b] at hh
    simpa only [sub_mul,mul_sub,smul_mul_assoc,mul_smul_comm,one_mul,mul_one,
      sub_left_inj] using hh
  have har : 0 ≤ a*(1-p) :=
    (show Commute a (1-p) from (Commute.one_right a).sub_right hac).mul_nonneg ha0
      (sub_nonneg.mpr hp.proj.le_one)
  have hal : 0 ≤ (1-a)*p :=
    ((Commute.one_left p).sub_left hac).mul_nonneg (sub_nonneg.mpr ha1) hp.proj.nonneg
  have hpa : a*p=c+(1/2:ℝ) • p := by
    dsimp [b] at hcp
    rw [sub_mul,smul_mul_assoc,one_mul] at hcp
    exact sub_eq_iff_eq_add.mp hcp
  have hlow : 0 ≤ a-(1/2:ℝ) • p := by
    have he : a-(1/2:ℝ) • p=c+a*(1-p) := by
      rw [mul_sub,mul_one,hpa]
      module
    rw [he]
    exact add_nonneg hc0 har
  have hhigh : 0 ≤ (1/2:ℝ) • (1:M)-(a-(1/2:ℝ) • p) := by
    have he : (1/2:ℝ) • (1:M)-(a-(1/2:ℝ) • p)=(1-a)*p+d := by
      rw [sub_mul,one_mul,hpa]
      have haa : a=c-d+(1/2:ℝ) • (1:M) := by
        exact (sub_eq_iff_eq_add.mp hb.symm)
      conv_lhs => rw [haa]
      module
    rw [he]
    exact add_nonneg hal hd0
  refine ⟨p,hp.proj,?_,?_,?_⟩
  · apply support_central hp
    exact central_posPart (central_sub ha (central_smul_real _ (fun x => Commute.one_left x)))
  · have hh := smul_nonneg (by norm_num : (0:ℝ) ≤ 2) hlow
    convert hh using 1; module
  · apply sub_nonneg.mp
    have hh := smul_nonneg (by norm_num : (0:ℝ) ≤ 2) hhigh
    convert hh using 1; module

include e in

theorem central_dyadic_digits (k : ℕ) (a : M) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (ha : Central a) :
    ∃ z : Fin (2^k) → M, (∀ i, IsStarProjection (z i)) ∧ (∀ i, Central (z i)) ∧
      0 ≤ (2:ℝ)^k • a-∑ i, z i ∧ (2:ℝ)^k • a-∑ i, z i ≤ 1 := by
  induction k generalizing a with
  | zero =>
    refine ⟨fun _ => 0,fun _ => IsStarProjection.zero M,fun _ x => Commute.zero_left x,?_,?_⟩ <;>
      simpa only [pow_zero,one_smul,Finset.sum_const_zero,sub_zero]
  | succ k ih =>
    obtain ⟨p,hp,hpc,hp0,hp1⟩ := exists_central_dyadic_projection e a ha0 ha1 ha
    obtain ⟨z,hz,hzc,hz0,hz1⟩ := ih ((2:ℝ) • a-p) hp0 hp1
      (central_sub (central_smul_real 2 ha) hpc)
    rw [pow_succ,Nat.mul_two]
    let y := Fin.append (fun _ : Fin (2^k) => p) z
    have hy (i : Fin (2^k+2^k)) : IsStarProjection (y i) := by
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa only [y,Fin.append_left] using hp
      · simpa only [y,Fin.append_right] using hz j
    have hyc (i : Fin (2^k+2^k)) : Central (y i) := by
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa only [y,Fin.append_left] using hpc
      · simpa only [y,Fin.append_right] using hzc j
    have he : (2:ℝ)^(k+1) • a-∑ i, y i = (2:ℝ)^k • ((2:ℝ) • a-p)-∑ i, z i := by
      simp only [y,Fin.sum_univ_add,Fin.append_left,Fin.append_right,Finset.sum_const,
        Finset.card_univ,Fintype.card_fin,←Nat.cast_smul_eq_nsmul ℝ,Nat.cast_pow,Nat.cast_ofNat,
        pow_succ,smul_sub,smul_smul]
      module
    refine ⟨y,hy,hyc,?_,?_⟩ <;> simpa only [←pow_succ,he] using (by assumption : _)
end PopaCenter

end

end OAI
