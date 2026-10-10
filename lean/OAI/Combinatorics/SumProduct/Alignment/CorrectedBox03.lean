import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.BoxPolynomial01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
noncomputable section
open _root_.Polynomial _root_.OAI.Polynomial
open scoped BigOperators
end
end
 

 
section
noncomputable section
open scoped BigOperators
namespace CorrectedBoxLeibman

 

theorem choose_short_scale (v L N₀ : ℕ) (δ ε A : ℝ) (hδ : 0<δ) (hε : 0<ε) (hA : 0≤A) :
    ∃ T N₁ : ℕ, 0<T ∧ 0<N₁ ∧ N₀≤N₁ ∧
      ∀ N : ℕ, N₁≤N → 0<N/T ∧ A/((N/T:ℕ):ℝ)≤ε ∧ N≤2*T*(N/T) ∧
        ∀ q : Fin v→Fin L, 2*((N/T:ℕ):ℝ)*(∑ i,(q i).val:ℕ)/N≤δ/8 := by
  obtain ⟨T,hT⟩ := exists_nat_ge (max 1 (16*(v:ℝ)*L/δ))
  obtain ⟨M,hM⟩ := exists_nat_ge (max 1 (A/ε))
  have hT1 : 1≤(T:ℝ) := (le_max_left _ _).trans hT
  have hM1 : 1≤(M:ℝ) := (le_max_left _ _).trans hM
  have hTp : 0<T := by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0:ℝ)<1) hT1)
  have hMp : 0<M := by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0:ℝ)<1) hM1)
  have hTb : 16*(v:ℝ)*L≤(T:ℝ)*δ := (div_le_iff₀ hδ).mp ((le_max_right _ _).trans hT)
  have hMb : A≤(M:ℝ)*ε := (div_le_iff₀ hε).mp ((le_max_right _ _).trans hM)
  refine ⟨T,max N₀ (T*M),hTp,lt_of_lt_of_le (Nat.mul_pos hTp hMp) (le_max_right _ _),le_max_left _ _,?_⟩
  intro N hN
  have hTM : T*M≤N := (le_max_right _ _).trans hN
  have hMH : M≤N/T := (Nat.le_div_iff_mul_le hTp).mpr (by simpa only [Nat.mul_comm] using hTM)
  have hH : 0<N/T := hMp.trans_le hMH
  have hTN : T≤N := by nlinarith only [hTM,hMp]
  obtain ⟨_,hHN,hNH⟩ := DenseBoxModularPolynomial.division_length hTp hTN
  have hNr : 0<(N:ℝ) := Nat.cast_pos.mpr (hTp.trans_le hTN)
  have hTr : 0<(T:ℝ) := Nat.cast_pos.mpr hTp
  refine ⟨hH,?_,hNH,?_⟩
  · calc
      _ ≤ A/(M:ℝ) := div_le_div_of_nonneg_left hA (Nat.cast_pos.mpr hMp)
        (by exact_mod_cast hMH)
      _ ≤ ε := (div_le_iff₀ (Nat.cast_pos.mpr hMp)).mpr
        (by simpa only [mul_comm] using hMb)
  · intro q
    have hsum : (∑ i,(q i).val:ℕ)≤v*L := by
      calc
        _ ≤ ∑ _ : Fin v, L := Finset.sum_le_sum (fun i _ => Nat.le_of_lt (q i).isLt)
        _ = _ := by simp
    have hratio : ((N/T:ℕ):ℝ)/(N:ℝ)≤1/(T:ℝ) := by
      apply (div_le_div_iff₀ hNr hTr).mpr
      simpa only [one_mul,Nat.cast_mul] using (show ((N/T:ℕ):ℝ)*(T:ℝ)≤N by exact_mod_cast hHN)
    calc
      _ = (2*(∑ i,(q i).val:ℕ):ℝ)*(((N/T:ℕ):ℝ)/(N:ℝ)) := by push_cast; ring
      _ ≤ (2*(∑ i,(q i).val:ℕ):ℝ)*(1/(T:ℝ)) :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ ≤ (2*((v*L:ℕ):ℝ))*(1/(T:ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast Nat.mul_le_mul_left 2 hsum
      _ ≤ δ/8 := by
        rw [one_div,← div_eq_mul_inv]
        apply (div_le_iff₀ hTr).mpr
        push_cast
        nlinarith only [hTb]

end CorrectedBoxLeibman
end
end
 

 
section
noncomputable section
open scoped BigOperators
namespace CorrectedBoxLeibman
open MvPolynomial
variable {v : ℕ} {E : Type*} [Fintype E] [DecidableEq E]
 
def monomialVector (m : E→(Fin v→₀ℕ)) (x : Fin v→ℚ) : E→ℚ :=
  fun e => (m e).prod (fun i k => x i^k)

def monomialPolynomial (m : E→(Fin v→₀ℕ)) (a : E→ℚ) : MvPolynomial (Fin v) ℚ :=
  ∑ e, monomial (m e) (a e)

lemma monomialPolynomial_coeff (m : E→(Fin v→₀ℕ)) (hm : Function.Injective m)
    (a : E→ℚ) (e : E) :
    (monomialPolynomial m a).coeff (m e)=a e := by
  classical
  simp only [monomialPolynomial,coeff_sum,coeff_monomial]
  simp only [hm.eq_iff]
  simp

omit [DecidableEq E] in
lemma monomialPolynomial_eval (m : E→(Fin v→₀ℕ)) (a : E→ℚ) (x : Fin v→ℚ) :
    eval x (monomialPolynomial m a)=∑ e, a e*monomialVector m x e := by
  simp [monomialPolynomial,monomialVector,eval_monomial]

 

theorem dense_monomial_unique (m : E→(Fin v→₀ℕ)) (hm : Function.Injective m)
    (D : ℕ) (hD : ∀ e, (m e).sum (fun _ k => k)≤D)
    (S : Finset ℚ) (Q : Finset (Fin v→ℚ))
    (hQ : Q⊆Fintype.piFinset (fun _ => S))
    (hdense : (D:ℚ≥0)/(S.card:ℚ≥0) < (Q.card:ℚ≥0)/(S.card:ℚ≥0)^v)
    (a : E→ℚ) (ha : ∀ x∈Q, ∑ e, a e*monomialVector m x e=0) : a=0 := by
  classical
  let P := monomialPolynomial m a
  have hdeg : P.totalDegree≤D := by
    apply MvPolynomial.totalDegree_finsetSum_le
    intro e _
    exact (totalDegree_monomial_le _ _).trans (hD e)
  have hz : P=0 := by
    by_contra hp
    have hbound := schwartz_zippel_totalDegree (n:=v) hp S
    have hsub : Q⊆(Fintype.piFinset (fun _ : Fin v => S)).filter (fun x => eval x P=0) := by
      intro x hx
      exact Finset.mem_filter.mpr ⟨hQ hx, (monomialPolynomial_eval m a x).trans (ha x hx)⟩
    have hc : (Q.card:ℚ≥0) ≤ ((Fintype.piFinset (fun _ : Fin v => S)).filter
        (fun x => eval x P=0)).card := by exact_mod_cast Finset.card_le_card hsub
    have hc' := div_le_div_of_nonneg_right hc (by positivity : (0:ℚ≥0)≤(S.card:ℚ≥0)^v)
    have hd' : (P.totalDegree:ℚ≥0)/(S.card:ℚ≥0)≤(D:ℚ≥0)/(S.card:ℚ≥0) :=
      div_le_div_of_nonneg_right (by exact_mod_cast hdeg) (by positivity)
    exact (not_lt_of_ge (hc'.trans (hbound.trans hd'))) hdense
  funext e
  have hh := monomialPolynomial_coeff m hm a e
  change P.coeff (m e)=a e at hh
  simpa only [hz,AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply,Pi.zero_apply] using hh.symm

lemma linear_form_coordinates (l : (E→ℚ)→ₗ[ℚ]ℚ) (x : E→ℚ) :
    l x = ∑ e, x e*l (Pi.single e 1) := by
  classical
  have he : x=∑ e, x e • (Pi.single e (1:ℚ) : E→ℚ) := by
    ext i
    simp [Finset.sum_apply,Pi.single_apply]
  conv_lhs => rw [he]
  simp

 

theorem dense_monomial_span (m : E→(Fin v→₀ℕ)) (hm : Function.Injective m)
    (D : ℕ) (hD : ∀ e, (m e).sum (fun _ k => k)≤D)
    (S : Finset ℚ) (Q : Finset (Fin v→ℚ))
    (hQ : Q⊆Fintype.piFinset (fun _ => S))
    (hdense : (D:ℚ≥0)/(S.card:ℚ≥0) < (Q.card:ℚ≥0)/(S.card:ℚ≥0)^v) :
    Submodule.span ℚ (Set.range (fun x : Q => monomialVector m x.val))=⊤ := by
  classical
  by_contra hne
  obtain ⟨l,hl,hker⟩ := Submodule.exists_le_ker_of_lt_top
    (Submodule.span ℚ (Set.range (fun x : Q => monomialVector m x.val))) (lt_top_iff_ne_top.mpr hne)
  let a : E→ℚ := fun e => l (Pi.single e 1)
  have ha : a=0 := by
    apply dense_monomial_unique m hm D hD S Q hQ hdense a
    intro x hx
    have he : l (monomialVector m x)=0 := hker (Submodule.subset_span ⟨⟨x,hx⟩,rfl⟩)
    rw [linear_form_coordinates] at he
    simpa only [a,mul_comm] using he
  apply hl
  apply LinearMap.ext
  intro x
  change l x=0
  rw [linear_form_coordinates]
  change (∑ e, x e*a e)=0
  rw [ha]
  simp

end CorrectedBoxLeibman
end
end
 

 
section
noncomputable section
open scoped BigOperators
namespace CorrectedBoxLeibman
variable {E V : Type*} [Fintype E] [DecidableEq E] [Fintype V]

 

lemma integer_weights_of_span (M : V→E→ℤ)
    (hspan : Submodule.span ℚ (Set.range (fun v : V => fun e => (M v e:ℚ)))=⊤) :
    ∃ B : ℕ, 0<B ∧ ∃ w : E→V→ℤ, ∀ e f,
      ∑ v, (w e v:ℝ)*(M v f:ℝ)=if e=f then (B:ℝ) else 0 := by
  classical
  have hex (e : E) : ∃ a : V→ℚ, ∑ v, a v • (fun f => (M v f:ℚ))=Pi.single e 1 := by
    apply (Submodule.mem_span_range_iff_exists_fun ℚ).mp
    rw [hspan]
    trivial
  choose a ha using hex
  obtain ⟨B,hB,w,hw⟩ := IntegerGridInterpolation.clear_denominators (fun p : E×V => a p.1 p.2)
  refine ⟨B,hB,fun e v => w (e,v),?_⟩
  intro e f
  have hid : ∑ v, a e v*(M v f:ℚ)=if e=f then 1 else 0 := by
    have hh := congrFun (ha e) f
    simpa [Finset.sum_apply,Pi.single_apply,eq_comm] using hh
  have hidR : ∑ v, (a e v:ℝ)*(M v f:ℝ)=if e=f then 1 else 0 := by
    have hh := congrArg (fun z : ℚ => (z:ℝ)) hid
    push_cast at hh
    split_ifs at hh ⊢ <;> simpa using hh
  have hwR (v : V) : (w (e,v):ℝ)=(B:ℝ)*(a e v:ℝ) := by
    exact_mod_cast (hw (e,v)).symm
  simp_rw [hwR,mul_assoc]
  rw [← Finset.mul_sum,hidR]
  split_ifs <;> simp

 

lemma homogeneous_recovery (deg : E→ℕ) (M : V→E→ℤ) (B : ℕ) (w : E→V→ℤ)
    (hw : ∀ e f, ∑ v, (w e v:ℝ)*(M v f:ℝ)=if e=f then (B:ℝ) else 0)
    (a : E→ℝ) (X A : ℝ) (hX : 0≤X)
    (hline : ∀ v j, 0<j →
      TriangularLatticeRecovery.circleNorm (∑ e, (if deg e=j then a e else 0)*(M v e:ℝ))*X^j≤A)
    (e : E) (he : 0<deg e) :
    TriangularLatticeRecovery.circleNorm ((B:ℝ)*a e)*X^(deg e)≤(∑ v, |(w e v:ℝ)|)*A := by
  classical
  rw [← TriangularLatticeRecovery.reconstruct_slice deg M w B hw a (deg e) e rfl]
  calc
    _ ≤ (∑ v, |(w e v:ℝ)| *TriangularLatticeRecovery.circleNorm
        (∑ f, (if deg f=deg e then a f else 0)*(M v f:ℝ)))*X^(deg e) :=
      mul_le_mul_of_nonneg_right (TriangularLatticeRecovery.integer_linear_bound _ _ _) (pow_nonneg hX _)
    _ = ∑ v, |(w e v:ℝ)| *(TriangularLatticeRecovery.circleNorm
        (∑ f, (if deg f=deg e then a f else 0)*(M v f:ℝ))*X^(deg e)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro v _
      ring
    _ ≤ ∑ v, |(w e v:ℝ)| *A := Finset.sum_le_sum (fun v _ =>
      mul_le_mul_of_nonneg_left (hline v (deg e) he) (abs_nonneg _))
    _ = _ := (Finset.sum_mul _ _ _).symm

end CorrectedBoxLeibman
end
end
 

 
section
noncomputable section
open scoped BigOperators
namespace CorrectedBoxLeibman
variable {v : ℕ} {E : Type*} [Fintype E] [DecidableEq E]

omit [Fintype E] [DecidableEq E] in
lemma monomialVector_eq_prod (m : E→(Fin v→₀ℕ)) (x : Fin v→ℚ) (e : E) :
    monomialVector m x e=∏ i, x i^(m e i) := by
  exact Finsupp.prod_fintype _ _ (by simp)

def gridMonomial (m : E→(Fin v→₀ℕ)) {L : ℕ} (x : Fin v→Fin L) (e : E) : ℤ :=
  ∏ i, ((x i).val:ℤ)^(m e i)

 

theorem dense_grid_integer_weights (m : E→(Fin v→₀ℕ)) (hm : Function.Injective m)
    (D : ℕ) (hD : ∀ e, (m e).sum (fun _ k => k)≤D)
    (L : ℕ) (Q : Finset (Fin v→Fin L))
    (hdense : (D:ℚ≥0)/(L:ℚ≥0) < (Q.card:ℚ≥0)/(L:ℚ≥0)^v) :
    ∃ B : ℕ, 0<B ∧ ∃ w : E→Q→ℤ, ∀ e f,
      ∑ x : Q, (w e x:ℝ)*(gridMonomial m x.val f:ℝ)=if e=f then (B:ℝ) else 0 := by
  classical
  let c : (Fin v→Fin L)→(Fin v→ℚ) := fun x i => ((x i).val:ℚ)
  have hc : Function.Injective c := by
    intro x y h
    funext i
    apply Fin.ext
    have hi := congrFun h i
    exact_mod_cast (show ((x i).val:ℚ)=((y i).val:ℚ) from hi)
  let S := (Finset.univ : Finset (Fin L)).image (fun i => (i.val:ℚ))
  let QR := Q.image c
  have hS : S.card=L := by
    rw [Finset.card_image_of_injective]
    · exact Fintype.card_fin L
    · intro a b h
      apply Fin.ext
      exact_mod_cast (show (a.val:ℚ)=(b.val:ℚ) from h)
  have hQR : QR.card=Q.card := Finset.card_image_of_injective Q hc
  have hsub : QR⊆Fintype.piFinset (fun _ => S) := by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    apply Fintype.mem_piFinset.mpr
    intro i
    exact Finset.mem_image.mpr ⟨y i,Finset.mem_univ _,rfl⟩
  have hspan := dense_monomial_span m hm D hD S QR hsub (by simpa only [hS,hQR] using hdense)
  apply integer_weights_of_span
  apply top_unique
  rw [← hspan]
  apply Submodule.span_mono
  rintro y ⟨x,rfl⟩
  obtain ⟨z,hz,hzx⟩ := Finset.mem_image.mp x.property
  refine ⟨⟨z,hz⟩,?_⟩
  ext e
  change (gridMonomial m z e:ℚ)=monomialVector m x.val e
  rw [monomialVector_eq_prod,← hzx]
  simp only [gridMonomial,Int.cast_prod,Int.cast_pow,Int.cast_natCast,c]

 

theorem uniform_dense_grid_weights (m : E→(Fin v→₀ℕ)) (hm : Function.Injective m)
    (D : ℕ) (hD : ∀ e, (m e).sum (fun _ k => k)≤D) (L : ℕ) :
    ∃ K : ℕ, 0<K ∧ ∀ Q : Finset (Fin v→Fin L),
      (D:ℚ≥0)/(L:ℚ≥0) < (Q.card:ℚ≥0)/(L:ℚ≥0)^v →
      ∃ B : ℕ, 0<B ∧ B≤K ∧ ∃ w : E→Q→ℤ,
        (∀ e f, ∑ x : Q, (w e x:ℝ)*(gridMonomial m x.val f:ℝ)=if e=f then (B:ℝ) else 0) ∧
        ∀ e, ∑ x : Q, |(w e x:ℝ)|≤K := by
  classical
  let T := {Q : Finset (Fin v→Fin L) //
      (D:ℚ≥0)/(L:ℚ≥0) < (Q.card:ℚ≥0)/(L:ℚ≥0)^v}
  have hex (Q : T) := dense_grid_integer_weights m hm D hD L Q.val Q.property
  choose B hB w hw using hex
  let k : T→ℕ := fun Q => B Q+∑ e, ∑ x : Q.val, (w Q e x).natAbs
  let K := 1+∑ Q : T, k Q
  have hK : 0<K := by dsimp [K]; omega
  refine ⟨K,hK,?_⟩
  intro Q hQ
  let t : T := ⟨Q,hQ⟩
  have hk : k t≤K := (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)).trans
    (Nat.le_add_left _ _)
  refine ⟨B t,hB t,?_,w t,hw t,?_⟩
  · exact (Nat.le_add_right _ _).trans hk
  · intro e
    have he : (∑ x : Q, (w t e x).natAbs)≤k t := by
      apply le_trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ e))
      exact Nat.le_add_left _ _
    have h := he.trans hk
    have hR : ((∑ x : Q, (w t e x).natAbs : ℕ):ℝ)≤K := by exact_mod_cast h
    have habs (z : ℤ) : (z.natAbs:ℝ)=|(z:ℝ)| := by
      simpa only [Int.cast_natCast,Int.cast_abs] using congrArg (fun z : ℤ => (z:ℝ)) (Int.natCast_natAbs z)
    simpa only [Nat.cast_sum,habs] using hR

end CorrectedBoxLeibman

end
end
end
end
end

end OAI
