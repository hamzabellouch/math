import OAI.Algebra.AffineCancellation.Modification

namespace OAI

noncomputable section

namespace ComplexCancellation.AffineModification
open MvPolynomial
variable (R : Type*) [CommRing R] (v : R)
attribute [local instance] MvPolynomial.weightedGradedAlgebra
def weight : Fin 2 → ℤ := ![-1,2]
def sourcePieces (e : ℤ) := weightedHomogeneousSubmodule R weight e
instance sourceGrading : GradedAlgebra (sourcePieces R) :=
  inferInstanceAs (GradedAlgebra (weightedHomogeneousSubmodule R weight))
lemma rel_homogeneous : rel R v ∈ sourcePieces R 0 := by
  apply IsWeightedHomogeneous.sub
  · convert ((isWeightedHomogeneous_X R weight 0).pow 2).mul
      (isWeightedHomogeneous_X R weight 1) using 1; norm_num [weight]
  · exact isWeightedHomogeneous_C _ _
lemma kernel_homogeneous : (RingHom.ker (π R v)).IsHomogeneous (sourcePieces R) := by
  change (RingHom.ker (Ideal.Quotient.mk (Ideal.span {rel R v}))).IsHomogeneous _
  rw [Ideal.mk_ker]
  apply Ideal.homogeneous_span
  intro r hr
  have he : r=rel R v := Set.mem_singleton_iff.mp hr
  subst r
  exact ⟨0,rel_homogeneous R v⟩
def pieces : ℤ → Submodule R (T R v) := QuotientGrading.pieces (sourcePieces R) (π R v)
instance grading : GradedAlgebra (pieces R v) := QuotientGrading.grading _ _
  (Ideal.Quotient.mkₐ_surjective R _) (kernel_homogeneous R v)
lemma monomial_image (d : Fin 2 →₀ ℕ) (r : R) :
    π R v (monomial d r)=τ R v^(d 0)*V R v^(d 1)*algebraMap R (T R v) r := by
  rw [monomial_eq]
  simp only [map_mul,AlgHom.commutes,MvPolynomial.C_eq_algebraMap]
  rw [Finsupp.prod_fintype]
  · simp only [Fin.prod_univ_two,map_mul,map_pow,τ,V]
    ring
  · intro i
    simp
lemma weight_eq (d : Fin 2 →₀ ℕ) :
    Finsupp.weight weight d = 2*(d 1 : ℤ)-(d 0 : ℤ) := by
  rw [Finsupp.weight_apply,Finsupp.sum_fintype]
  · simp [Fin.sum_univ_two,weight]
    ring
  · intro i
    simp
lemma monomial_reduction (i h m : ℕ) :
    τ R v^(i+2*m)*V R v^(h+m)=τ R v^i*V R v^h*algebraMap R (T R v) (v^m) := by
  rw [map_pow,← equation R v,pow_add,pow_add,pow_mul,mul_pow]
  ring
lemma piece_negative (n : ℕ) {r : T R v} (hr : r ∈ pieces R v (-(n:ℤ))) :
    ∃ s : R, r=τ R v^n*algebraMap R (T R v) s := by
  obtain ⟨p,hp,rfl⟩ := hr
  induction hp using IsWeightedHomogeneous.induction_on with
  | zero => exact ⟨0,by simp⟩
  | add p q hp hq ihp ihq =>
    obtain ⟨a,ha⟩ := ihp
    obtain ⟨b,hb⟩ := ihq
    exact ⟨a+b,by rw [map_add,map_add,ha,hb,mul_add]⟩
  | monomial d a hd =>
    rw [weight_eq] at hd
    have hi : d 0=n+2*d 1 := by omega
    refine ⟨v^(d 1)*a,?_⟩
    change π R v (monomial d a)=_
    rw [monomial_image,hi]
    have he := monomial_reduction R v n 0 (d 1)
    simpa only [zero_add,pow_zero,mul_one,map_mul,mul_assoc] using congrArg (fun x => x*algebraMap R (T R v) a) he
lemma piece_even (n : ℕ) {r : T R v} (hr : r ∈ pieces R v (2*(n:ℤ))) :
    ∃ s : R, r=V R v^n*algebraMap R (T R v) s := by
  obtain ⟨p,hp,rfl⟩ := hr
  induction hp using IsWeightedHomogeneous.induction_on with
  | zero => exact ⟨0,by simp⟩
  | add p q hp hq ihp ihq =>
    obtain ⟨a,ha⟩ := ihp
    obtain ⟨b,hb⟩ := ihq
    exact ⟨a+b,by rw [map_add,map_add,ha,hb,mul_add]⟩
  | monomial d a hd =>
    rw [weight_eq] at hd
    have hi : d 0=2*(d 1-n) := by omega
    have hh : d 1=n+(d 1-n) := by omega
    refine ⟨v^(d 1-n)*a,?_⟩
    change π R v (monomial d a)=_
    rw [monomial_image,hi]
    conv_lhs => arg 1; arg 2; rw [hh]
    have he := monomial_reduction R v 0 n (d 1-n)
    simpa only [zero_add,pow_zero,one_mul,map_mul,mul_assoc] using congrArg (fun x => x*algebraMap R (T R v) a) he
lemma piece_odd (n : ℕ) {r : T R v} (hr : r ∈ pieces R v (2*(n:ℤ)+1)) :
    ∃ s : R, r=τ R v*V R v^(n+1)*algebraMap R (T R v) s := by
  obtain ⟨p,hp,rfl⟩ := hr
  induction hp using IsWeightedHomogeneous.induction_on with
  | zero => exact ⟨0,by simp⟩
  | add p q hp hq ihp ihq =>
    obtain ⟨a,ha⟩ := ihp
    obtain ⟨b,hb⟩ := ihq
    exact ⟨a+b,by rw [map_add,map_add,ha,hb,mul_add]⟩
  | monomial d a hd =>
    rw [weight_eq] at hd
    have hi : d 0=1+2*(d 1-(n+1)) := by omega
    have hh : d 1=(n+1)+(d 1-(n+1)) := by omega
    refine ⟨v^(d 1-(n+1))*a,?_⟩
    change π R v (monomial d a)=_
    rw [monomial_image,hi]
    conv_lhs => arg 1; arg 2; rw [hh]
    have he := monomial_reduction R v 1 (n+1) (d 1-(n+1))
    simpa only [pow_one,map_mul,mul_assoc] using congrArg (fun x => x*algebraMap R (T R v) a) he
lemma degree_cases (e : ℤ) :
    (∃ n : ℕ, e=-(n+1:ℤ)) ∨ (∃ n : ℕ, e=2*(n:ℤ)) ∨ (∃ n : ℕ, e=2*(n:ℤ)+1) := by
  by_cases hn : e < 0
  · exact Or.inl ⟨(-e-1).toNat,by omega⟩
  · by_cases hm : e%2=0
    · exact Or.inr (Or.inl ⟨(e/2).toNat,by omega⟩)
    · exact Or.inr (Or.inr ⟨(e/2).toNat,by omega⟩)
lemma piece_monomial (e : ℤ) : ∃ i h : ℕ, ∀ r ∈ pieces R v e,
    ∃ s : R, r=τ R v^i*V R v^h*algebraMap R (T R v) s := by
  rcases degree_cases e with ⟨n,rfl⟩ | ⟨n,rfl⟩ | ⟨n,rfl⟩
  · refine ⟨n+1,0,?_⟩
    intro r hr
    have hr' : r ∈ pieces R v (-((n+1:ℕ):ℤ)) := by simpa using hr
    simpa using piece_negative R v (n+1) hr'
  · refine ⟨0,n,?_⟩
    intro r hr
    simpa using piece_even R v n hr
  · refine ⟨1,n+1,?_⟩
    intro r hr
    simpa using piece_odd R v n hr
lemma V_dvd_of_positive {r : T R v} {e : ℤ} (he : 0 < e) (hr : r ∈ pieces R v e) :
    V R v ∣ r := by
  rcases degree_cases e with ⟨n,hen⟩ | ⟨n,hen⟩ | ⟨n,hen⟩
  · omega
  · rw [hen] at hr
    have hn : 1 ≤ n := by omega
    obtain ⟨s,rfl⟩ := piece_even R v n hr
    exact dvd_mul_of_dvd_left (dvd_pow_self _ (by omega : n ≠ 0)) _
  · rw [hen] at hr
    obtain ⟨s,rfl⟩ := piece_odd R v n hr
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (dvd_pow_self _ (by omega : n+1 ≠ 0)) _) _
lemma degree_even_of_not_τ_dvd {r : T R v} {e : ℤ} (hr : r ∈ pieces R v e)
    (h : ¬τ R v ∣ r) : ∃ n : ℕ, e=2*(n:ℤ) := by
  rcases degree_cases e with ⟨n,hen⟩ | he | ⟨n,hen⟩
  · exfalso
    apply h
    rw [hen] at hr
    have hr' : r ∈ pieces R v (-((n+1:ℕ):ℤ)) := by simpa using hr
    obtain ⟨s,rfl⟩ := piece_negative R v (n+1) hr'
    exact dvd_mul_of_dvd_left (dvd_pow_self _ (by omega : n+1 ≠ 0)) _
  · exact he
  · exfalso
    apply h
    rw [hen] at hr
    obtain ⟨s,rfl⟩ := piece_odd R v n hr
    exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
lemma coefficient_mem (r : R) : algebraMap R (T R v) r ∈ pieces R v 0 :=
  ⟨C r,isWeightedHomogeneous_C _ _,(π R v).commutes r⟩
lemma τ_mem : τ R v ∈ pieces R v (-1) := ⟨X 0,isWeightedHomogeneous_X R weight 0,rfl⟩
lemma V_mem : V R v ∈ pieces R v 2 := ⟨X 1,isWeightedHomogeneous_X R weight 1,rfl⟩
end ComplexCancellation.AffineModification

end

end OAI
