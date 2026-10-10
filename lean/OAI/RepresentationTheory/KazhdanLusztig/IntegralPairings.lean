import OAI.RepresentationTheory.KazhdanLusztig.BottSamelson

namespace OAI

/-!
Hilbert recurrences, projective section ranges, integral lattices and graded perfect adjoints.
-/

section

namespace KLInvariance.Hilbert
open Polynomial

 theorem hasSum_shift_coeff {f : ℤ → ℝ} {q c : ℝ} (hq : q≠0)
    (hf : HasSum (fun n : ℤ => f n*q^n) c) (d : ℤ) :
    HasSum (fun n : ℤ => f (n-d)*q^n) (q^d*c) := by
  apply (Equiv.addRight d).hasSum_iff.mp
  apply (hf.mul_left (q^d)).congr_fun
  intro n
  change f (n+d-d)*q^(n+d)=q^d*(f n*q^n)
  rw [add_sub_cancel_right,zpow_add₀ hq]
  ring

 theorem numerator_unique (f : ℤ → ℕ) (F G : ℤ[X]) (D : ℝ → ℝ)
    (hD : ∀ q, 0<q → q<1 → D q≠0)
    (hF : ∀ q, 0<q → q<1 → HasSum (fun n : ℤ => (f n : ℝ)*q^n)
      (eval₂ (Int.castRingHom ℝ) q F*D q))
    (hG : ∀ q, 0<q → q<1 → HasSum (fun n : ℤ => (f n : ℝ)*q^n)
      (eval₂ (Int.castRingHom ℝ) q G*D q)) : F=G := by
  apply Polynomial.map_injective (Int.castRingHom ℝ) Int.cast_injective
  apply Polynomial.eq_of_infinite_eval_eq
  apply Set.Infinite.mono (s := Set.Ioo (0 : ℝ) 1) ?_ (Set.Ioo_infinite (by norm_num))
  intro q hq
  have he := (hF q hq.1 hq.2).unique (hG q hq.1 hq.2)
  change eval q (F.map (Int.castRingHom ℝ))=eval q (G.map (Int.castRingHom ℝ))
  simpa only [eval_map] using (mul_right_cancel₀ (hD q hq.1 hq.2) he)

 theorem numerator_add_shift (f g h : ℤ → ℕ) (F G H : ℤ[X]) (D : ℝ → ℝ)
    (hD : ∀ q, 0<q → q<1 → D q≠0)
    (hF : ∀ q, 0<q → q<1 → HasSum (fun n : ℤ => (f n : ℝ)*q^n)
      (eval₂ (Int.castRingHom ℝ) q F*D q))
    (hG : ∀ q, 0<q → q<1 → HasSum (fun n : ℤ => (g n : ℝ)*q^n)
      (eval₂ (Int.castRingHom ℝ) q G*D q))
    (hH : ∀ q, 0<q → q<1 → HasSum (fun n : ℤ => (h n : ℝ)*q^n)
      (eval₂ (Int.castRingHom ℝ) q H*D q))
    (he : ∀ n, f n=g n+h (n-1)) : F=G+X*H := by
  apply Polynomial.map_injective (Int.castRingHom ℝ) Int.cast_injective
  apply Polynomial.eq_of_infinite_eval_eq
  apply Set.Infinite.mono (s := Set.Ioo (0 : ℝ) 1) ?_ (Set.Ioo_infinite (by norm_num))
  intro q hq
  have hh := hasSum_shift_coeff hq.1.ne' (hH q hq.1 hq.2) 1
  have hs := (hG q hq.1 hq.2).add hh
  have hf := hF q hq.1 hq.2
  have heq : eval₂ (Int.castRingHom ℝ) q F*D q=
      eval₂ (Int.castRingHom ℝ) q G*D q+q*(eval₂ (Int.castRingHom ℝ) q H*D q) := by
    rw [zpow_one] at hs
    apply hf.unique
    apply hs.congr_fun
    intro n
    rw [he,Nat.cast_add,add_mul]
  change eval q (F.map (Int.castRingHom ℝ))=eval q ((G+X*H).map (Int.castRingHom ℝ))
  simp only [eval_map,eval₂_add,eval₂_mul,eval₂_X]
  apply mul_right_cancel₀ (hD q hq.1 hq.2)
  calc
    _ = eval₂ (Int.castRingHom ℝ) q G*D q+q*(eval₂ (Int.castRingHom ℝ) q H*D q) := heq
    _ = _ := by ring

end KLInvariance.Hilbert

end


section

/-! Exact polynomial character recurrences for the actual integral word stalks.
These are the unnormalized Hecke coefficients for multiplication by T_s+1.
They are proved from the projection lattices, not from the KL conjecture. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 theorem bottStalk_finrank_descent (i : I) (l : List I) (x : W)
    (h : cs.length (cs.simple i*x)<cs.length x) (n : ℤ) :
    Module.finrank ℝ (bottStalkPiece cs basis (i::l) x n)=
      Module.finrank ℝ (bottStalkPiece cs basis l (cs.simple i*x) n)+
      Module.finrank ℝ (bottStalkPiece cs basis l x (n-1)) := by
  have hdim := Hilbert.finrank_exact (A := ℝ) (bottStalkPiece cs basis (i::l) x)
    (bottStalkPiece cs basis l (cs.simple i*x)) (bottHeadRight cs i l x)
    (bottHeadRight_homogeneous cs basis i l x) (bottHeadRight_surjective cs i l x) n
  have hk := finrank_homogeneousEquiv (k := ℝ)
    (N := LinearMap.ker (bottHeadRight cs i l x)) (bottStalkPiece cs basis l x)
    (bottHeadRightKernelPiece cs basis i l x) (bottHeadRightKernelEquiv cs i l x h) 1
    (bottHeadRightKernelEquiv_homogeneous cs basis i l x h) n
  change Module.finrank ℝ (bottStalkPiece cs basis (i::l) x n)=
    Module.finrank ℝ (bottHeadRightKernelPiece cs basis i l x n)+
      Module.finrank ℝ (bottStalkPiece cs basis l (cs.simple i*x) n) at hdim
  rw [hk] at hdim
  omega

 theorem bottStalkCharacter_ascent (i : I) (l : List I) (x : W)
    (h : cs.length x<cs.length (cs.simple i*x)) :
    bottStalkCharacter cs basis (i::l) x=bottStalkCharacter cs basis l x+
      Polynomial.X*bottStalkCharacter cs basis l (cs.simple i*x) := by
  apply Hilbert.numerator_add_shift
    (fun n => Module.finrank ℝ (bottStalkPiece cs basis (i::l) x n))
    (fun n => Module.finrank ℝ (bottStalkPiece cs basis l x n))
    (fun n => Module.finrank ℝ (bottStalkPiece cs basis l (cs.simple i*x) n))
    _ _ _ (fun q => (1-q)⁻¹ ^ Fintype.card σ)
  · intro q _ hq
    exact pow_ne_zero _ (inv_ne_zero (sub_ne_zero.mpr (ne_of_gt hq)))
  · exact fun _ => bottStalkCharacter_hasSum cs basis (i::l) x
  · exact fun _ => bottStalkCharacter_hasSum cs basis l x
  · exact fun _ => bottStalkCharacter_hasSum cs basis l (cs.simple i*x)
  · exact bottStalk_finrank_ascent cs basis i l x h

 theorem bottStalkCharacter_descent (i : I) (l : List I) (x : W)
    (h : cs.length (cs.simple i*x)<cs.length x) :
    bottStalkCharacter cs basis (i::l) x=bottStalkCharacter cs basis l (cs.simple i*x)+
      Polynomial.X*bottStalkCharacter cs basis l x := by
  apply Hilbert.numerator_add_shift
    (fun n => Module.finrank ℝ (bottStalkPiece cs basis (i::l) x n))
    (fun n => Module.finrank ℝ (bottStalkPiece cs basis l (cs.simple i*x) n))
    (fun n => Module.finrank ℝ (bottStalkPiece cs basis l x n))
    _ _ _ (fun q => (1-q)⁻¹ ^ Fintype.card σ)
  · intro q _ hq
    exact pow_ne_zero _ (inv_ne_zero (sub_ne_zero.mpr (ne_of_gt hq)))
  · exact fun _ => bottStalkCharacter_hasSum cs basis (i::l) x
  · exact fun _ => bottStalkCharacter_hasSum cs basis l (cs.simple i*x)
  · exact fun _ => bottStalkCharacter_hasSum cs basis l x
  · exact bottStalk_finrank_descent cs basis i l x h

end
end KLInvariance.TitsSpace

end


section

/-! The honest unnormalized Hecke word (T_s+1)...(T_t+1), including exact
coefficient recurrence over a general commutative ring, without invertibility
of q or any KL/BMP character assertion. -/
namespace KLInvariance.HeckeQ
open Hecke (Space basis)
variable {I W C : Type*} [Group W] {M : CoxeterMatrix I} [CommRing C]
noncomputable section

 theorem left_coeff (cs : CoxeterSystem M W) (q : C) (i : I) (v : Space W C) (x : W) :
    left cs q i v x =
      if cs.length (cs.simple i*x)<cs.length x then v (cs.simple i*x)+(q-1)*v x
      else q*v (cs.simple i*x) := by
  classical
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v v' hv hv' =>
    simp only [map_add,Finsupp.add_apply,hv,hv']
    split_ifs <;> ring
  | single w c =>
    have hc : Finsupp.single w c=c • (basis w : Space W C) := by
      simp [basis,Finsupp.smul_single]
    rw [hc,map_smul,left_basis]
    by_cases h : w=cs.simple i*x
    · subst w
      have hd : cs.length (cs.simple i*(cs.simple i*x))<cs.length (cs.simple i*x) ↔
          ¬cs.length (cs.simple i*x)<cs.length x := by
        simp only [cs.simple_mul_simple_cancel_left]
        have := cs.length_simple_mul x i
        omega
      have hn : cs.simple i*x≠x := by
        intro he
        have := cs.length_simple_mul x i
        rw [he] at this
        omega
      simp only [Finsupp.smul_apply,smul_eq_mul,basis,Finsupp.single_apply,
        cs.simple_mul_simple_cancel_left,hn,ite_false]
      have hlength := cs.length_simple_mul x i
      split_ifs <;> try omega
      all_goals simp [Ne.symm hn] <;> try ring
    · have hn : cs.simple i*w≠x := by
        intro he
        apply h
        rw [←he]
        simp
      by_cases hw : w=x
      · subst w
        simp only [Finsupp.smul_apply,smul_eq_mul,basis,Finsupp.single_apply,
          Ne.symm hn,ite_false]
        split_ifs <;> simp [Ne.symm hn] ; try ring
      · simp only [Finsupp.smul_apply,smul_eq_mul,basis,Finsupp.single_apply,
          h,hw,ite_false]
        split_ifs <;> simp [hn,hw]

 theorem left_plus_coeff (cs : CoxeterSystem M W) (q : C) (i : I)
    (v : Space W C) (x : W) :
    (v+left cs q i v) x = if cs.length (cs.simple i*x)<cs.length x then
      v (cs.simple i*x)+q*v x else v x+q*v (cs.simple i*x) := by
  rw [Finsupp.add_apply,left_coeff]
  split_ifs <;> ring

 def positiveWord (cs : CoxeterSystem M W) (q : C) : List I → Space W C
  | [] => basis 1
  | i::l => positiveWord cs q l+left cs q i (positiveWord cs q l)

 @[simp] theorem positiveWord_nil (cs : CoxeterSystem M W) (q : C) :
    positiveWord cs q []=basis 1 := rfl

 theorem positiveWord_cons_coeff (cs : CoxeterSystem M W) (q : C) (i : I)
    (l : List I) (x : W) :
    positiveWord cs q (i::l) x = if cs.length (cs.simple i*x)<cs.length x then
      positiveWord cs q l (cs.simple i*x)+q*positiveWord cs q l x
      else positiveWord cs q l x+q*positiveWord cs q l (cs.simple i*x) :=
  left_plus_coeff cs q i (positiveWord cs q l) x

end
end KLInvariance.HeckeQ

end


section

/-! Genuine word stalk normalization and identification with the honest
Hecke word. This does not identify the indecomposable BMP character with KL. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

 theorem bottStalkCharacter_zero (l : List I) (x : W)
    [Subsingleton (bottStalk cs l x)] : bottStalkCharacter cs basis l x=0 := by
  apply Hilbert.numerator_unique
    (fun n => Module.finrank ℝ (bottStalkPiece cs basis l x n)) _ _
    (fun q => (1-q)⁻¹ ^ Fintype.card σ)
  · intro q _ hq
    exact pow_ne_zero _ (inv_ne_zero (sub_ne_zero.mpr (ne_of_gt hq)))
  · exact fun _ => bottStalkCharacter_hasSum cs basis l x
  · intro q _ _
    simpa only [Module.finrank_zero_of_subsingleton,Nat.cast_zero,zero_mul,Polynomial.eval₂_zero] using (hasSum_zero : HasSum (fun _ : ℤ => (0 : ℝ)) 0)

 def bottTopPolynomialEquiv (l : List I) (hl : cs.IsReduced l) :
    bottStalk cs l (cs.wordProd l) ≃ₗ[ℝ] MvPolynomial σ ℝ :=
  ((bottTopStalkEquiv cs l hl).restrictScalars ℝ).trans
    (SymmetricAlgebra.equivMvPolynomial basis).toLinearEquiv

omit [Fintype σ] in
 theorem bottTopPolynomialEquiv_homogeneous (l : List I) (hl : cs.IsReduced l)
    (n : ℤ) (s : bottStalk cs l (cs.wordProd l)) (hs : s∈bottStalkPiece cs basis l (cs.wordProd l) n) :
    bottTopPolynomialEquiv cs basis l hl s∈polynomialGrading ℝ σ n := by
  apply (mem_symmetricGrading basis n _).mp
  exact (bottTopStalkEquiv_homogeneous cs basis l hl n s).mpr hs

 theorem bottStalkCharacter_top (l : List I) (hl : cs.IsReduced l) :
    bottStalkCharacter cs basis l (cs.wordProd l)=1 := by
  have hd (n : ℤ) : Module.finrank ℝ (bottStalkPiece cs basis l (cs.wordProd l) n)=
      Module.finrank ℝ (polynomialGrading ℝ σ n) := by
    have hh := finrank_homogeneousEquiv (bottStalkPiece cs basis l (cs.wordProd l))
      (polynomialGrading ℝ σ) (bottTopPolynomialEquiv cs basis l hl) 0
      (fun n s hs => by simpa only [add_zero] using bottTopPolynomialEquiv_homogeneous cs basis l hl n s hs) n
    have hz : n-(0:ℤ)=n := Int.sub_zero n
    rw [hz] at hh
    exact hh.symm
  apply Hilbert.numerator_unique
    (fun n => Module.finrank ℝ (bottStalkPiece cs basis l (cs.wordProd l) n)) _ _
    (fun q => (1-q)⁻¹ ^ Fintype.card σ)
  · intro q _ hq
    exact pow_ne_zero _ (inv_ne_zero (sub_ne_zero.mpr (ne_of_gt hq)))
  · exact fun _ => bottStalkCharacter_hasSum cs basis l (cs.wordProd l)
  · intro q hq hq1
    simpa only [hd,Polynomial.eval₂_one,one_mul] using Hilbert.hasSum_polynomial ℝ σ hq.le hq1

 theorem bottStalkCharacter_nil (x : W) :
    bottStalkCharacter cs basis [] x=if x=1 then 1 else 0 := by
  classical
  by_cases hx : x=1
  · subst x
    simpa using bottStalkCharacter_top cs basis [] (by simp [CoxeterSystem.IsReduced])
  · let := bottStalk_nil_subsingleton cs x hx
    rw [ite_eq_right hx]
    exact bottStalkCharacter_zero cs basis [] x

 theorem bottStalkCharacter_eq_heckeWord (l : List I) (x : W) :
    bottStalkCharacter cs basis l x=HeckeQ.positiveWord cs (Polynomial.X : Polynomial ℤ) l x := by
  classical
  induction l generalizing x with
  | nil => simp only [bottStalkCharacter_nil,HeckeQ.positiveWord_nil,Hecke.basis,
      Finsupp.single_apply]; split_ifs <;> simp_all
  | cons i l ih =>
    rw [HeckeQ.positiveWord_cons_coeff]
    by_cases hd : cs.length (cs.simple i*x)<cs.length x
    · rw [ite_eq_left hd,bottStalkCharacter_descent cs basis i l x hd,ih,ih]
    · have ha : cs.length x<cs.length (cs.simple i*x) := by
        have := cs.length_simple_mul x i
        omega
      rw [ite_eq_right hd,bottStalkCharacter_ascent cs basis i l x ha,ih,ih]

end
end KLInvariance.TitsSpace

end


section

/-! Range-valued projections to sets of coordinates and their natural
surjective restriction maps. -/
namespace KLInvariance.CoordinateProjection
universe ur un uv ux
variable {R : Type ur} [CommRing R] {N : Type un} [AddCommGroup N] [Module R N]
  {V : Type uv} {X : V → Type ux} [∀ x, AddCommGroup (X x)] [∀ x, Module R (X x)]
  (f : ∀ x, N →ₗ[R] X x)
noncomputable section

 def eval (U : Set V) : N →ₗ[R] (∀ x : U, X x.val) := LinearMap.pi (fun x => f x.val)
 def image (U : Set V) : Submodule R (∀ x : U, X x.val) := LinearMap.range (eval f U)
 def project (U : Set V) : N →ₗ[R] image f U := (eval f U).rangeRestrict

 theorem project_surjective (U : Set V) : Function.Surjective (project f U) :=
by
  rintro ⟨z,n,hn⟩
  exact ⟨n,Subtype.ext hn⟩

 @[simp] theorem project_apply (U : Set V) (n : N) (x : U) : (project f U n).val x=f x.val n := rfl

 theorem project_zero_iff (U : Set V) (n : N) : project f U n=0 ↔ ∀ x∈U, f x n=0 := by
  constructor
  · intro h x hx
    exact congrArg (fun z : image f U => z.val ⟨x,hx⟩) h
  · intro h
    apply Subtype.ext
    funext x
    exact h x.val x.property

 def restrict {U K : Set V} (h : U⊆K) : image f K →ₗ[R] image f U where
  toFun z := ⟨fun x => z.val ⟨x.val,h x.property⟩,by
    obtain ⟨n,hn⟩ := z.property
    refine ⟨n,?_⟩
    funext x
    exact congrFun hn ⟨x.val,h x.property⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

 @[simp] theorem restrict_project {U K : Set V} (h : U⊆K) (n : N) :
    restrict f h (project f K n)=project f U n := rfl

 theorem restrict_surjective {U K : Set V} (h : U⊆K) : Function.Surjective (restrict f h) := by
  intro z
  obtain ⟨n,rfl⟩ := project_surjective f U z
  exact ⟨project f K n,rfl⟩

 theorem restrict_zero_iff {U K : Set V} (h : U⊆K) (z : image f K) :
    restrict f h z=0 ↔ ∀ x hx, x∈U → z.val ⟨x,hx⟩=0 := by
  constructor
  · intro hz x hx hu
    exact congrArg (fun q : image f U => q.val ⟨x,hu⟩) hz
  · intro hz
    apply Subtype.ext
    funext x
    exact hz x.val (h x.property) x.property

end
end KLInvariance.CoordinateProjection

end


section

/-! Upper sets and actual finite-word projection predicates. -/
namespace KLInvariance.TitsSpace
open Module CoordinateProjection
universe u v
variable {I : Type u} [klPreservedInstance11 : Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 def BruhatUpper (U : Set W) : Prop :=
  ∀ {x y}, BruhatLE cs x y → x∈U → y∈U

 def simpleUnion (i : I) (U : Set W) : Set W := {x | x∈U ∨ cs.simple i*x∈U}
 def simpleInter (i : I) (U : Set W) : Set W := {x | x∈U ∧ cs.simple i*x∈U}

 omit [Fintype I] in
 theorem BruhatUpper.mem_simpleUnion (U : Set W) (hU : BruhatUpper cs U) (i : I) (x : W) :
    x∈simpleUnion cs i U ↔ upperSimple cs i x∈U := by
  constructor
  · rintro (hx|hx)
    · exact hU (le_upperSimple cs i x) hx
    · have hh := hU (le_upperSimple cs i (cs.simple i*x)) hx
      simpa only [upperSimple_mul] using hh
  · intro hx
    classical
    unfold upperSimple at hx
    split_ifs at hx with h
    · exact Or.inl hx
    · exact Or.inr hx

 omit [Fintype I] in
 theorem BruhatUpper.mem_simpleInter (U : Set W) (hU : BruhatUpper cs U) (i : I) (x : W) :
    x∈simpleInter cs i U ↔ lowerSimple cs i x∈U := by
  constructor
  · rintro ⟨hx,hsx⟩
    classical
    unfold lowerSimple
    split_ifs <;> assumption
  · intro hx
    refine ⟨hU (lowerSimple_le cs i x) hx,?_⟩
    have he : lowerSimple cs i (cs.simple i*x)∈U := by simpa only [lowerSimple_mul] using hx
    exact hU (lowerSimple_le cs i (cs.simple i*x)) he

include klPreservedInstance11 in
 theorem BruhatUpper.simpleUnion (U : Set W) (hU : BruhatUpper cs U) (i : I) :
    BruhatUpper cs (simpleUnion cs i U) := by
  have _ := klPreservedInstance11
  intro x y hxy hx
  exact (hU.mem_simpleUnion cs U i y).mpr
    (hU (upperSimple_mono cs i hxy) ((hU.mem_simpleUnion cs U i x).mp hx))

include klPreservedInstance11 in
 theorem BruhatUpper.simpleInter (U : Set W) (hU : BruhatUpper cs U) (i : I) :
    BruhatUpper cs (simpleInter cs i U) := by
  have _ := klPreservedInstance11
  intro x y hxy hx
  exact (hU.mem_simpleInter cs U i y).mpr
    (hU (lowerSimple_mono cs i hxy) ((hU.mem_simpleInter cs U i x).mp hx))

 omit [Fintype I] in
 theorem simpleUnion_stable (i : I) (U : Set W) (x : W) :
    cs.simple i*x∈simpleUnion cs i U ↔ x∈simpleUnion cs i U := by
  change (cs.simple i*x∈U ∨ cs.simple i*(cs.simple i*x)∈U) ↔ (x∈U ∨ cs.simple i*x∈U)
  rw [cs.simple_mul_simple_cancel_left,or_comm]

 omit [Fintype I] in
 theorem simpleInter_stable (i : I) (U : Set W) (x : W) :
    cs.simple i*x∈simpleInter cs i U ↔ x∈simpleInter cs i U := by
  change (cs.simple i*x∈U ∧ cs.simple i*(cs.simple i*x)∈U) ↔ (x∈U ∧ cs.simple i*x∈U)
  rw [cs.simple_mul_simple_cancel_left,and_comm]

 omit [Fintype I] in
 theorem cross_edge_is_simple (U : Set W) (hU : BruhatUpper cs U) (i : I)
    {x y : W} (hxy : BruhatStep cs x y) (hsx : cs.simple i*x∈U)
    (hsy : cs.simple i*y∉U) : y=cs.simple i*x := by
  by_contra he
  exact hsy (hU (.single (bruhatStep_simple_mul cs hxy i he)) hsx)

 def bottSetImage (l : List I) (U : Set W) := image (bottStalkProjection cs l) U
 instance bottSetImageAddCommGroup (l : List I) (U : Set W) : AddCommGroup (bottSetImage cs l U) :=
  Submodule.addCommGroup _
 instance bottSetImageModule (l : List I) (U : Set W) : Module (SymmetricCoefficient (M := M)) (bottSetImage cs l U) :=
  Submodule.module _

 def bottSetProjection (l : List I) (U : Set W) : BottSamelsonModule cs l →ₗ[
    SymmetricCoefficient (M := M)] bottSetImage cs l U := project (bottStalkProjection cs l) U

 def BottCompatible (l : List I) (U : Set W) (z : ∀ x : U, bottStalk cs l x.val) : Prop :=
  ∀ (x y : W) (hx : x∈U) (hy : y∈U), BruhatStep cs x y →
    ∃ m : BottSamelsonModule cs l,
      bottStalkProjection cs l x m=z ⟨x,hx⟩ ∧ bottStalkProjection cs l y m=z ⟨y,hy⟩

 def BottFlabby (l : List I) : Prop :=
  ∀ U, BruhatUpper cs U → ∀ z, BottCompatible cs l U z → z∈bottSetImage cs l U

 def BottProjectiveUpper (l : List I) : Prop :=
  ∀ U, BruhatUpper cs U → Module.Projective (SymmetricCoefficient (M := M)) (bottSetImage cs l U)

end
end KLInvariance.TitsSpace

end


section

/-! Explicit linear descent and split exact sequences for projected modules. -/
namespace KLInvariance.ProjectiveRange
universe ur um up uq
variable {R : Type ur} [CommRing R]
  {M : Type um} [AddCommGroup M] [Module R M]
  {P : Type up} [AddCommGroup P] [Module R P]
  {Q : Type uq} [AddCommGroup Q] [Module R Q]
noncomputable section

 def descend (f : M →ₗ[R] P) (hf : Function.Surjective f) (g : M →ₗ[R] Q)
    (hg : ∀ m, f m=0 → g m=0) : P →ₗ[R] Q :=
  ((LinearMap.ker f).liftQ g hg).comp (f.quotKerEquivOfSurjective hf).symm.toLinearMap

 theorem descend_apply (f : M →ₗ[R] P) (hf : Function.Surjective f) (g : M →ₗ[R] Q)
    (hg : ∀ m, f m=0 → g m=0) (m : M) : descend f hf g hg (f m)=g m := by
  change (LinearMap.ker f).liftQ g hg ((f.quotKerEquivOfSurjective hf).symm (f m))=g m
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
  rfl

 theorem projective_of_end (f : M →ₗ[R] P) (hf : Function.Surjective f)
    [Module.Projective R M] (e : Module.End R M)
    (he : ∀ m, f (e m)=f m) (hz : ∀ m, f m=0 → e m=0) : Module.Projective R P := by
  apply Module.Projective.of_split (descend f hf e hz) f
  apply LinearMap.ext
  intro p
  obtain ⟨m,rfl⟩ := hf p
  rw [LinearMap.comp_apply,descend_apply,he,LinearMap.id_apply]

 def kernelRetraction (f : M →ₗ[R] P) (s : P →ₗ[R] M)
    (hs : ∀ p, f (s p)=p) : M →ₗ[R] LinearMap.ker f :=
  (LinearMap.id-s.comp f).codRestrict (LinearMap.ker f) (fun m => by
    change f (m-s (f m))=0
    rw [map_sub,hs,sub_self])

 theorem kernel_projective (f : M →ₗ[R] P) (hf : Function.Surjective f)
    [Module.Projective R M] [Module.Projective R P] : Module.Projective R (LinearMap.ker f) := by
  obtain ⟨s,hs⟩ := Module.projective_lifting_property f (LinearMap.id : P →ₗ[R] P) hf
  have hs' : ∀ p, f (s p)=p := LinearMap.congr_fun hs
  apply Module.Projective.of_split (LinearMap.ker f).subtype (kernelRetraction f s hs')
  apply LinearMap.ext
  intro m
  apply Subtype.ext
  change (m : M)-s (f m)=m
  rw [m.property,map_zero,sub_zero]

 def splitEquiv (f : M →ₗ[R] P) (s : P →ₗ[R] M) (hs : ∀ p, f (s p)=p) :
    M ≃ₗ[R] (LinearMap.ker f × P) :=
  { (kernelRetraction f s hs).prod f with
    invFun := fun z => z.1.val+s z.2
    left_inv := fun m => sub_add_cancel m (s (f m))
    right_inv := by
      intro z
      apply Prod.ext
      · apply Subtype.ext
        change z.1.val+s z.2-s (f (z.1.val+s z.2))=z.1.val
        rw [map_add,z.1.property,zero_add,hs]
        exact add_sub_cancel_right _ _
      · change f (z.1.val+s z.2)=z.2
        rw [map_add,z.1.property,zero_add,hs] }

 theorem projective_of_kernel (f : M →ₗ[R] P) (hf : Function.Surjective f)
    [Module.Projective R P] [Module.Projective R (LinearMap.ker f)] : Module.Projective R M := by
  obtain ⟨s,hs⟩ := Module.projective_lifting_property f (LinearMap.id : P →ₗ[R] P) hf
  exact Module.Projective.of_equiv (splitEquiv f s (LinearMap.congr_fun hs)).symm

end
end KLInvariance.ProjectiveRange

end


section

namespace KLInvariance.ReflectionPairTranslation
open TensorProduct
universe uc ua un
variable {C : Type uc} [CommRing C] {A : Type ua} [CommRing A] [Algebra C A]
  {N : Type un} [AddCommGroup N] [Module A N] [Module C N] [IsScalarTower C A N]
  (τ : A ≃+* A) (hfix : ∀ c : C, τ (algebraMap C A c)=algebraMap C A c)
noncomputable section

 theorem tensorFirst_map (e : Module.End A N) (m : A ⊗[C] N) :
    tensorFirst (C := C) (AlgebraTensorModule.map (LinearMap.id : A →ₗ[A] A) (e.restrictScalars C) m)=
      e (tensorFirst (C := C) m) := by
  induction m using TensorProduct.inductionOn with
  | add m n hm hn => simp only [map_add,hm,hn]
  | tmul a n => simp only [AlgebraTensorModule.map_tmul,LinearMap.id_apply,
      LinearMap.restrictScalars_apply,tensorFirst_tmul,map_smul]

 theorem tensorSecond_map (e : Module.End A N) (m : A ⊗[C] N) :
    tensorSecond τ hfix (AlgebraTensorModule.map (LinearMap.id : A →ₗ[A] A) (e.restrictScalars C) m)=
      twistMap τ e (tensorSecond τ hfix m) := by
  induction m using TensorProduct.inductionOn with
  | add m n hm hn => simp only [map_add,hm,hn]
  | tmul a n =>
    simp only [AlgebraTensorModule.map_tmul,LinearMap.id_apply,
      LinearMap.restrictScalars_apply,tensorSecond_tmul]
    apply Twist.ext
    exact (map_smul e (τ a) n).symm

end
end KLInvariance.ReflectionPairTranslation

end


section

namespace KLInvariance
universe ur un up uq
variable {R : Type ur} [CommRing R]
  {N : Type un} [klPreservedInstance12 : AddCommGroup N] [Module R N]
  {P : Type up} [klPreservedInstance13 : AddCommGroup P] [Module R P]
  {Q : Type uq} [klPreservedInstance14 : AddCommGroup Q] [Module R Q]
 theorem injective_of_zero_lift (f : N →ₗ[R] P) (hf : Function.Surjective f) (g : P →ₗ[R] Q)
    (h : ∀ n, g (f n)=0 → f n=0) : Function.Injective g := by
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro p hp
  obtain ⟨n,rfl⟩ := hf p
  exact h n hp
 theorem maps_eq_iff_of_zero_iff (f : N →ₗ[R] P) (g : N →ₗ[R] Q)
    (h : ∀ n, f n=0 ↔ g n=0) (m n : N) : f m=f n ↔ g m=g n := by
  rw [← sub_eq_zero,← map_sub,h,map_sub,sub_eq_zero]
include klPreservedInstance12 klPreservedInstance13 klPreservedInstance14 in
 theorem functions_eq_of_surjective (f : N → P) (hf : Function.Surjective f)
    (g h : P → Q) (he : ∀ n, g (f n)=h (f n)) (p : P) : g p=h p := by
  have _ := klPreservedInstance12
  have _ := klPreservedInstance13
  have _ := klPreservedInstance14
  obtain ⟨n,rfl⟩ := hf p
  exact he n
end KLInvariance

end


section

/-! Genuine first/reflected-tail maps on projected upper-set images. -/
namespace KLInvariance.TitsSpace
open Module TensorProduct FrobeniusDuality ReflectionFrobenius ReflectionPairTranslation
open CoordinateProjection ProjectiveRange
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section
attribute [local instance] restrictedModule restrictedTower restrictedFree restrictedFinite

 def simplePull (i : I) (U : Set W) : Set W := {x | cs.simple i*x∈U}

 theorem bottSetProjection_zero_iff (l : List I) (U : Set W) (m : BottSamelsonModule cs l) :
    bottSetProjection cs l U m=0 ↔ ∀ x∈U, bottStalkProjection cs l x m=0 :=
  project_zero_iff _ _ _

 theorem bottSetProjection_surjective (l : List I) (U : Set W) :
    Function.Surjective (bottSetProjection cs l U) := project_surjective _ _

 theorem bottStalkProjection_zero_of_eq (l : List I) {x y : W} (h : x=y)
    (m : BottSamelsonModule cs l) (hm : bottStalkProjection cs l x m=0) :
    bottStalkProjection cs l y m=0 := by
  subst y
  exact hm

 theorem bottHeadSet_zero_iff (i : I) (l : List I) (U : Set W)
    (m : BottSamelsonModule cs (i::l)) :
    bottSetProjection cs (i::l) U m=0 ↔
      bottSetProjection cs l U (bottHeadTail cs i l m)=0 ∧
      bottSetProjection cs l (simplePull cs i U) (bottHeadReflectedTail cs i l m).val=0 := by
  constructor
  · intro hm
    have h := (bottSetProjection_zero_iff cs (i::l) U m).mp hm
    refine ⟨?_,?_⟩
    · apply (bottSetProjection_zero_iff cs l U _).mpr
      intro x hx
      exact congrArg Prod.fst ((bottHeadLocalPair_zero_iff cs i l x m).mp (h x hx))
    · apply (bottSetProjection_zero_iff cs l (simplePull cs i U) _).mpr
      intro x hx
      have hh : bottStalkProjection cs l (cs.simple i*(cs.simple i*x))
          (bottHeadReflectedTail cs i l m).val=0 := congrArg (fun z => z.2.val)
        ((bottHeadLocalPair_zero_iff cs i l (cs.simple i*x) m).mp (h _ hx))
      exact bottStalkProjection_zero_of_eq cs l (cs.simple_mul_simple_cancel_left i) _ hh
  · rintro ⟨hp,hq⟩
    apply (bottSetProjection_zero_iff cs (i::l) U m).mpr
    intro x hx
    apply (bottHeadLocalPair_zero_iff cs i l x m).mpr
    apply Prod.ext
    · exact (bottSetProjection_zero_iff cs l U _).mp hp x hx
    · apply Twist.ext
      exact (bottSetProjection_zero_iff cs l (simplePull cs i U) _).mp hq (cs.simple i*x)
        (by simpa only [simplePull,Set.mem_ofPred_eq,cs.simple_mul_simple_cancel_left] using hx)

 def bottSetFirst (i : I) (l : List I) (U : Set W) : bottSetImage cs (i::l) U →ₗ[
    SymmetricCoefficient (M := M)] bottSetImage cs l U :=
  descend (bottSetProjection cs (i::l) U) (bottSetProjection_surjective cs (i::l) U)
    ((bottSetProjection cs l U).comp (bottHeadTail cs i l))
    (fun m hm => ((bottHeadSet_zero_iff cs i l U m).mp hm).1)

 def bottSetSecond (i : I) (l : List I) (U : Set W) : bottSetImage cs (i::l) U →ₗ[
    SymmetricCoefficient (M := M)]
    Twist (coefficientAction cs (cs.simple i)).toRingEquiv (bottSetImage cs l (simplePull cs i U)) :=
  descend (bottSetProjection cs (i::l) U) (bottSetProjection_surjective cs (i::l) U)
    ((twistMap (coefficientAction cs (cs.simple i)).toRingEquiv
      (bottSetProjection cs l (simplePull cs i U))).comp (bottHeadReflectedTail cs i l))
    (fun m hm => Twist.ext (((bottHeadSet_zero_iff cs i l U m).mp hm).2))

 theorem bottSetFirst_project (i : I) (l : List I) (U : Set W) (m : BottSamelsonModule cs (i::l)) :
    bottSetFirst cs i l U (bottSetProjection cs (i::l) U m)=
      bottSetProjection cs l U (bottHeadTail cs i l m) := descend_apply _ _ _ _ m

 theorem bottSetSecond_project (i : I) (l : List I) (U : Set W) (m : BottSamelsonModule cs (i::l)) :
    bottSetSecond cs i l U (bottSetProjection cs (i::l) U m)=
      Twist.mk (bottSetProjection cs l (simplePull cs i U) (bottHeadReflectedTail cs i l m).val) :=
  descend_apply _ _ _ _ m

 theorem bottSetComponents_injective (i : I) (l : List I) (U : Set W) :
    Function.Injective ((bottSetFirst cs i l U).prod (bottSetSecond cs i l U)) := by
  apply injective_of_zero_lift (bottSetProjection cs (i::l) U)
    (bottSetProjection_surjective cs (i::l) U)
  intro m hz
  apply (bottHeadSet_zero_iff cs i l U m).mpr
  have hp := congrArg Prod.fst hz
  have hq := congrArg (fun z => z.2.val) hz
  exact ⟨(bottSetFirst_project cs i l U m).symm.trans hp,
    (congrArg Twist.val (bottSetSecond_project cs i l U m)).symm.trans hq⟩

 def bottTensorEnd (i : I) (l : List I)
    (e : Module.End (SymmetricCoefficient (M := M)) (BottSamelsonModule cs l)) :
    Module.End (SymmetricCoefficient (M := M)) (BottSamelsonModule cs (i::l)) :=
  AlgebraTensorModule.map (LinearMap.id : SymmetricCoefficient (M := M) →ₗ[
    SymmetricCoefficient (M := M)] SymmetricCoefficient (M := M)) (e.restrictScalars (simpleFixed cs i))

 theorem bottTensorEnd_seed (i : I) (l : List I)
    (e : Module.End (SymmetricCoefficient (M := M)) (BottSamelsonModule cs l))
    (n : BottSamelsonModule cs l) :
    bottTensorEnd cs i l e ((1 : SymmetricCoefficient (M := M)) ⊗ₜ[simpleFixed cs i] n)=
      (1 : SymmetricCoefficient (M := M)) ⊗ₜ[simpleFixed cs i] e n := rfl

 theorem bottTensorEnd_first (i : I) (l : List I)
    (e : Module.End (SymmetricCoefficient (M := M)) (BottSamelsonModule cs l))
    (m : BottSamelsonModule cs (i::l)) :
    bottHeadTail cs i l (bottTensorEnd cs i l e m)=e (bottHeadTail cs i l m) :=
  tensorFirst_map e m

 theorem bottTensorEnd_second (i : I) (l : List I)
    (e : Module.End (SymmetricCoefficient (M := M)) (BottSamelsonModule cs l))
    (m : BottSamelsonModule cs (i::l)) :
    bottHeadReflectedTail cs i l (bottTensorEnd cs i l e m)=
      twistMap (coefficientAction cs (cs.simple i)).toRingEquiv e (bottHeadReflectedTail cs i l m) :=
  tensorSecond_map (coefficientAction cs (cs.simple i)).toRingEquiv (fun c => c.property) e m

 theorem bottHead_components_injective (i : I) (l : List I)
    (m : BottSamelsonModule cs (i::l))
    (hp : bottHeadTail cs i l m=0) (hq : bottHeadReflectedTail cs i l m=0) : m=0 := by
  apply bottEvaluation_injective cs (i::l)
  funext e
  have hz : bottStalkProjection cs (i::l) (bottWeight cs (i::l) e) m=0 := by
    apply (bottHeadLocalPair_zero_iff cs i l _ m).mpr
    rw [bottHeadLocalPair_value,hp,hq]
    apply Prod.ext
    · exact map_zero _
    · apply Twist.ext
      exact map_zero _
  exact congrArg (fun z => z.val ⟨e,rfl⟩) hz

end
end KLInvariance.TitsSpace

end


section

namespace KLInvariance.ReflectionPairTranslation
open TensorProduct
universe uc ua un
variable {C : Type uc} [CommRing C] {A : Type ua} [CommRing A] [Algebra C A]
  {N : Type un} [AddCommGroup N] [Module A N] [Module C N] [IsScalarTower C A N]
  (τ : A ≃+* A) (hfix : ∀ c : C, τ (algebraMap C A c)=algebraMap C A c)
noncomputable section
 theorem tensor_difference (α : A) (hdiv : ∀ a : A, α ∣ a-τ a)
    (m : A ⊗[C] N) :
    ∃ n : N, tensorFirst (C := C) m-(tensorSecond τ hfix m).val=α • n := by
  induction m using TensorProduct.inductionOn with
  | add m n hm hn =>
    obtain ⟨p,hp⟩ := hm
    obtain ⟨q,hq⟩ := hn
    refine ⟨p+q,?_⟩
    simp only [map_add]
    change (tensorFirst (C := C) m+tensorFirst (C := C) n)-
      ((tensorSecond τ hfix m).val+(tensorSecond τ hfix n).val)=α • (p+q)
    rw [add_sub_add_comm,hp,hq,smul_add]
  | tmul a n =>
    obtain ⟨b,hb⟩ := hdiv a
    refine ⟨b • n,?_⟩
    change a • n-τ a • n=α • (b • n)
    rw [← sub_smul,hb,mul_smul]
end
end KLInvariance.ReflectionPairTranslation

end


section

namespace KLInvariance.PairProjection
universe u v w z
variable {R : Type u} [CommRing R]
  {N : Type v} [AddCommGroup N] [Module R N]
  {X : Type w} [AddCommGroup X] [Module R X]
  {Y : Type z} [AddCommGroup Y] [Module R Y]
  (f : N →ₗ[R] X) (g : N →ₗ[R] Y)

 theorem cross_lift (α : R) (hann : ∀ z : Edge f g, α • z=0)
    (p q : N) (h : ∃ n : N, p-q=α • n) :
    ∃ n : N, f n=f q ∧ g n=g p := by
  apply (compatible_iff f g _ _).mp
  obtain ⟨n,hn⟩ := h
  have hd := congrArg ((lower f g).comp f) hn
  simp only [LinearMap.comp_apply,map_sub,map_smul,hann] at hd
  exact (sub_eq_zero.mp hd).symm.trans (compatible f g p)

end KLInvariance.PairProjection

end


section

/-! Honest head/tail gluing. An exclusive-part crossing can only be the
simple head edge; alpha-divisibility handles precisely that crossing. -/
namespace KLInvariance.TitsSpace
open Module CoordinateProjection ReflectionPairTranslation
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section
open FrobeniusDuality ReflectionFrobenius
attribute [local instance] restrictedModule restrictedTower restrictedFree restrictedFinite

 theorem bottHead_difference (i : I) (l : List I) (m : BottSamelsonModule cs (i::l)) :
    ∃ n : BottSamelsonModule cs l,
      bottHeadTail cs i l m-(bottHeadReflectedTail cs i l m).val=simpleRootPolynomial (M := M) i • n :=
  tensor_difference (coefficientAction cs (cs.simple i)).toRingEquiv (fun c => c.property)
    (simpleRootPolynomial (M := M) i) (simple_divisible cs i) m

 def bottHeadPatch (i : I) (l : List I) (U : Set W) (m : BottSamelsonModule cs (i::l)) :
    ∀ x : simpleUnion cs i U, bottStalk cs l x.val := by
  classical
  exact fun x => if x.val∈U then bottStalkProjection cs l x.val (bottHeadTail cs i l m)
    else bottStalkProjection cs l x.val (bottHeadReflectedTail cs i l m).val

 theorem bottHeadPatch_compatible (i : I) (l : List I) (U : Set W) (hU : BruhatUpper cs U)
    (m : BottSamelsonModule cs (i::l))
    (hJ : ∀ x∈simpleInter cs i U,
      bottStalkProjection cs l x (bottHeadTail cs i l m)=
        bottStalkProjection cs l x (bottHeadReflectedTail cs i l m).val) :
    BottCompatible cs l (simpleUnion cs i U) (bottHeadPatch cs i l U m) := by
  classical
  intro x y hx hy hxy
  by_cases hxU : x∈U
  · have hyU := hU (.single hxy) hxU
    simp only [bottHeadPatch,ite_eq_left hxU,ite_eq_left hyU]
    exact ⟨bottHeadTail cs i l m,rfl,rfl⟩
  · by_cases hyU : y∈U
    · simp only [bottHeadPatch,ite_eq_right hxU,ite_eq_left hyU]
      by_cases hsy : cs.simple i*y∈U
      · exact ⟨(bottHeadReflectedTail cs i l m).val,rfl,(hJ y ⟨hyU,hsy⟩).symm⟩
      · have he := cross_edge_is_simple cs U hU i hxy (hx.resolve_left hxU) hsy
        subst y
        exact PairProjection.cross_lift _ _ (simpleRootPolynomial (M := M) i)
          (bottReflectionEdge_annihilated cs l x (cs.simple i) (simple_represents cs i))
          (bottHeadTail cs i l m) (bottHeadReflectedTail cs i l m).val (bottHead_difference cs i l m)
    · simp only [bottHeadPatch,ite_eq_right hxU,ite_eq_right hyU]
      exact ⟨(bottHeadReflectedTail cs i l m).val,rfl,rfl⟩

 theorem bottHeadPatch_lift (i : I) (l : List I) (H : BottFlabby cs l)
    (U : Set W) (hU : BruhatUpper cs U) (m : BottSamelsonModule cs (i::l))
    (hJ : ∀ x∈simpleInter cs i U,
      bottStalkProjection cs l x (bottHeadTail cs i l m)=
        bottStalkProjection cs l x (bottHeadReflectedTail cs i l m).val) :
    ∃ n : BottSamelsonModule cs l,
      (∀ x∈U, bottStalkProjection cs l x n=bottStalkProjection cs l x (bottHeadTail cs i l m)) ∧
      (∀ x∈simplePull cs i U,
        bottStalkProjection cs l x n=bottStalkProjection cs l x (bottHeadReflectedTail cs i l m).val) := by
  classical
  obtain ⟨n,hn⟩ := H (simpleUnion cs i U) (hU.simpleUnion cs U i)
    (bottHeadPatch cs i l U m) (bottHeadPatch_compatible cs i l U hU m hJ)
  refine ⟨n,?_,?_⟩
  · intro x hx
    have hh := congrFun hn ⟨x,Or.inl hx⟩
    simpa only [CoordinateProjection.eval,LinearMap.pi_apply,bottHeadPatch,ite_eq_left hx] using hh
  · intro x hx
    have hh := congrFun hn ⟨x,Or.inr hx⟩
    by_cases hxU : x∈U
    · have hh' : bottStalkProjection cs l x n=bottStalkProjection cs l x (bottHeadTail cs i l m) := by
        simpa only [CoordinateProjection.eval,LinearMap.pi_apply,bottHeadPatch,ite_eq_left hxU] using hh
      exact hh'.trans (hJ x ⟨hxU,hx⟩)
    · simpa only [CoordinateProjection.eval,LinearMap.pi_apply,bottHeadPatch,ite_eq_right hxU] using hh

end
end KLInvariance.TitsSpace

end


section

namespace KLInvariance.TitsSpace
open Module TensorProduct CoordinateProjection ReflectionPairTranslation
open FrobeniusDuality ReflectionFrobenius
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section
attribute [local instance] restrictedModule restrictedTower restrictedFree restrictedFinite

 def bottSetRestrict (l : List I) {U K : Set W} (h : U⊆K) :
    bottSetImage cs l K →ₗ[SymmetricCoefficient (M := M)] bottSetImage cs l U :=
  restrict (bottStalkProjection cs l) h

 theorem bottSetRestrict_project (l : List I) {U K : Set W} (h : U⊆K)
    (n : BottSamelsonModule cs l) :
    bottSetRestrict cs l h (bottSetProjection cs l K n)=bottSetProjection cs l U n := rfl

 theorem bottSetRestrict_surjective (l : List I) {U K : Set W} (h : U⊆K) :
    Function.Surjective (bottSetRestrict cs l h) := restrict_surjective _ h

 theorem bottSetRestrict_zero_iff (l : List I) {U K : Set W} (h : U⊆K)
    (z : bottSetImage cs l K) : bottSetRestrict cs l h z=0 ↔
      ∀ x hx, x∈U → z.val ⟨x,hx⟩=0 := restrict_zero_iff (bottStalkProjection cs l) h z

 def bottSeed (i : I) (l : List I) (n : BottSamelsonModule cs l) :
    BottSamelsonModule cs (i::l) := (1 : SymmetricCoefficient (M := M)) ⊗ₜ[simpleFixed cs i] n

 theorem bottSeed_first (i : I) (l : List I) (n : BottSamelsonModule cs l) :
    bottHeadTail cs i l (bottSeed cs i l n)=n := bottHeadTail_seed cs i l n

 theorem bottSeed_second (i : I) (l : List I) (n : BottSamelsonModule cs l) :
    bottHeadReflectedTail cs i l (bottSeed cs i l n)=Twist.mk n := bottHeadReflectedTail_seed cs i l n

 theorem bottSetFirst_seed (i : I) (l : List I) (U : Set W) (n : BottSamelsonModule cs l) :
    bottSetFirst cs i l U (bottSetProjection cs (i::l) U (bottSeed cs i l n))=
      bottSetProjection cs l U n :=
  (bottSetFirst_project cs i l U _).trans
    (congrArg (bottSetProjection cs l U) (bottSeed_first cs i l n))

 theorem bottSetSecond_seed (i : I) (l : List I) (U : Set W) (n : BottSamelsonModule cs l) :
    bottSetSecond cs i l U (bottSetProjection cs (i::l) U (bottSeed cs i l n))=
      Twist.mk (bottSetProjection cs l (simplePull cs i U) n) :=
  (bottSetSecond_project cs i l U _).trans
    (congrArg (fun t => Twist.mk (bottSetProjection cs l (simplePull cs i U) t.val))
      (bottSeed_second cs i l n))

 theorem bottSeed_zero_stable (i : I) (l : List I) (U : Set W)
    (hU : ∀ x, cs.simple i*x∈U ↔ x∈U)
    (n : BottSamelsonModule cs l) (hn : bottSetProjection cs l U n=0) :
    bottSetProjection cs (i::l) U (bottSeed cs i l n)=0 := by
  apply (bottHeadSet_zero_iff cs i l U _).mpr
  constructor
  · exact (congrArg (bottSetProjection cs l U) (bottSeed_first cs i l n)).trans hn
  · apply ((congrArg (fun t => bottSetProjection cs l (simplePull cs i U) t.val)
      (bottSeed_second cs i l n)).trans ·)
    apply (bottSetProjection_zero_iff cs l (simplePull cs i U) n).mpr
    intro x hx
    exact (bottSetProjection_zero_iff cs l U n).mp hn x ((hU x).mp hx)

 theorem bottSetFirst_restrict (i : I) (l : List I) {U K : Set W} (h : U⊆K)
    (z : bottSetImage cs (i::l) K) :
    bottSetFirst cs i l U (bottSetRestrict cs (i::l) h z)=
      bottSetRestrict cs l h (bottSetFirst cs i l K z) := by
  refine functions_eq_of_surjective (bottSetProjection cs (i::l) K)
    (bottSetProjection_surjective cs (i::l) K)
    (fun z => bottSetFirst cs i l U (bottSetRestrict cs (i::l) h z))
    (fun z => bottSetRestrict cs l h (bottSetFirst cs i l K z)) ?_ z
  intro m
  exact (bottSetFirst_project cs i l U m).trans
    (congrArg (bottSetRestrict cs l h) (bottSetFirst_project cs i l K m)).symm

 theorem bottSeed_zero_inter (i : I) (l : List I) (U : Set W)
    (n : BottSamelsonModule cs l) (hn : bottSetProjection cs l U n=0) :
    bottSetProjection cs (i::l) (simpleInter cs i U) (bottSeed cs i l n)=0 := by
  apply (bottHeadSet_zero_iff cs i l (simpleInter cs i U) _).mpr
  have h := (bottSetProjection_zero_iff cs l U n).mp hn
  constructor
  · apply ((congrArg (bottSetProjection cs l (simpleInter cs i U))
      (bottSeed_first cs i l n)).trans ·)
    apply (bottSetProjection_zero_iff cs l (simpleInter cs i U) n).mpr
    intro x hx
    exact h x hx.1
  · apply ((congrArg (fun t => bottSetProjection cs l (simplePull cs i (simpleInter cs i U)) t.val)
      (bottSeed_second cs i l n)).trans ·)
    apply (bottSetProjection_zero_iff cs l (simplePull cs i (simpleInter cs i U)) n).mpr
    intro x hx
    exact h x (by simpa only [cs.simple_mul_simple_cancel_left] using hx.2)

end
end KLInvariance.TitsSpace

end


section

namespace KLInvariance
universe ur um un up
variable {R : Type ur} [CommRing R]
  {M : Type um} [AddCommGroup M] [Module R M]
  {N : Type un} [AddCommGroup N] [Module R N]
  {P : Type up} [AddCommGroup P] [Module R P]
noncomputable section
 theorem projective_of_same_range (f : M →ₗ[R] P) (hf : Function.Injective f)
    (g : N →ₗ[R] P) (hg : Function.Injective g) (h : LinearMap.range f=LinearMap.range g)
    [Module.Projective R N] : Module.Projective R M :=
  Module.Projective.of_equiv (((LinearEquiv.ofInjective g hg).trans
    (LinearEquiv.ofEq _ _ h.symm)).trans (LinearEquiv.ofInjective f hf).symm)

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

namespace ReflectionPairTranslation.Twist
 theorem projective (τ : R ≃+* R) [Module.Projective R N] : Module.Projective R (Twist τ N) := by
  let : RingHomInvPair τ.symm.toRingHom τ.toRingHom := RingHomInvPair.of_ringEquiv_symm τ
  let : RingHomInvPair τ.toRingHom τ.symm.toRingHom := RingHomInvPair.of_ringEquiv τ
  exact Module.Projective.of_equiv (σ' := τ.toRingHom) (equiv τ N)
end ReflectionPairTranslation.Twist
end
end KLInvariance

end


section

namespace KLInvariance
universe ur um uh up us
variable {R : Type ur} [CommRing R]
  {M : Type um} [AddCommGroup M] [Module R M]
  {H : Type uh} [AddCommGroup H] [Module R H]
  {P : Type up} [AddCommGroup P] [Module R P]
  {S : Type us} [AddCommGroup S] [Module R S]

 theorem kernel_coordinate_injective (f : M →ₗ[R] P) (g : M →ₗ[R] S)
    (h : Function.Injective (f.prod g)) :
    Function.Injective (g.comp (LinearMap.ker f).subtype) := by
  intro m n he
  apply Subtype.ext
  apply h
  exact Prod.ext (m.property.trans n.property.symm) he

 theorem common_kernel_coordinate_injective (r : M →ₗ[R] H) (f : M →ₗ[R] P) (g : M →ₗ[R] S)
    (h : Function.Injective (f.prod g)) :
    Function.Injective (g.comp (LinearMap.ker r ⊓ LinearMap.ker f).subtype) := by
  intro m n he
  apply Subtype.ext
  apply h
  exact Prod.ext (m.property.2.trans n.property.2.symm) he

 theorem projective_of_coordinates (f : M →ₗ[R] P) (hf : Function.Injective f)
    (g : H →ₗ[R] P) (hg : Function.Injective g)
    (hfg : ∀ m, ∃ n, f m=g n) (hgf : ∀ n, ∃ m, f m=g n)
    [Module.Projective R H] : Module.Projective R M := by
  apply projective_of_same_range f hf g hg
  ext p
  constructor
  · rintro ⟨m,rfl⟩
    obtain ⟨n,hn⟩ := hfg m
    exact ⟨n,hn.symm⟩
  · rintro ⟨n,rfl⟩
    exact hgf n

namespace ReflectionPairTranslation
 theorem twistMap_injective (τ : R ≃+* R) (f : M →ₗ[R] P) (hf : Function.Injective f) :
    Function.Injective (twistMap τ f) := by
  intro m n h
  exact Twist.ext (hf (congrArg Twist.val h))
end ReflectionPairTranslation

namespace CoordinateProjection
universe uv ux
variable {V : Type uv} {X : V → Type ux} [∀ x, AddCommGroup (X x)] [∀ x, Module R (X x)]
  (f : ∀ x, M →ₗ[R] X x)
 theorem restrict_joint_injective {U V' K : Set V} (hU : U⊆K) (hV : V'⊆K)
    (hc : ∀ x∈K, x∈U ∨ x∈V') :
    Function.Injective ((restrict f hU).prod (restrict f hV)) := by
  intro p q h
  apply Subtype.ext
  funext x
  rcases hc x.val x.property with hx|hx
  · exact congrArg (fun z : image f U => z.val ⟨x.val,hx⟩) (congrArg Prod.fst h)
  · exact congrArg (fun z : image f V' => z.val ⟨x.val,hx⟩) (congrArg Prod.snd h)
end CoordinateProjection
end KLInvariance

end


section

namespace KLInvariance.TitsSpace
open Module CoordinateProjection ReflectionPairTranslation
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 def bottInterRestriction (i : I) (l : List I) (U : Set W) :
    bottSetImage cs l U →ₗ[SymmetricCoefficient (M := M)] bottSetImage cs l (simpleInter cs i U) :=
  bottSetRestrict cs l (fun _ h => h.1)

 def bottUnionRestriction (i : I) (l : List I) (U : Set W) :
    bottSetImage cs l (simpleUnion cs i U) →ₗ[SymmetricCoefficient (M := M)] bottSetImage cs l U :=
  bottSetRestrict cs l (fun _ h => Or.inl h)

 def bottUnionPullRestriction (i : I) (l : List I) (U : Set W) :
    bottSetImage cs l (simpleUnion cs i U) →ₗ[SymmetricCoefficient (M := M)]
      bottSetImage cs l (simplePull cs i U) :=
  bottSetRestrict cs l (fun _ h => Or.inr h)

 def bottCommonKernel (i : I) (l : List I) (U : Set W) :
    Submodule (SymmetricCoefficient (M := M)) (bottSetImage cs (i::l) U) :=
  LinearMap.ker (bottInterRestriction cs i (i::l) U) ⊓ LinearMap.ker (bottSetFirst cs i l U)

 def bottCommonSecond (i : I) (l : List I) (U : Set W) :
    bottCommonKernel cs i l U →ₗ[SymmetricCoefficient (M := M)]
      Twist (coefficientAction cs (cs.simple i)).toRingEquiv (bottSetImage cs l (simplePull cs i U)) :=
  (bottSetSecond cs i l U).comp (bottCommonKernel cs i l U).subtype

 theorem bottCommonSecond_injective (i : I) (l : List I) (U : Set W) :
    Function.Injective (bottCommonSecond cs i l U) :=
  common_kernel_coordinate_injective _ _ _ (bottSetComponents_injective cs i l U)

 def bottUnionKernelSecond (i : I) (l : List I) (U : Set W) :
    LinearMap.ker (bottUnionRestriction cs i l U) →ₗ[SymmetricCoefficient (M := M)]
      bottSetImage cs l (simplePull cs i U) :=
  (bottUnionPullRestriction cs i l U).comp (LinearMap.ker (bottUnionRestriction cs i l U)).subtype

 theorem bottUnionKernelSecond_injective (i : I) (l : List I) (U : Set W) :
    Function.Injective (bottUnionKernelSecond cs i l U) := by
  apply kernel_coordinate_injective
  exact restrict_joint_injective (bottStalkProjection cs l)
    (fun _ h => Or.inl h) (fun _ h => Or.inr h) (fun _ h => h)

 theorem bottHeadPatch_lift_of_zero_inter (i : I) (l : List I) (H : BottFlabby cs l)
    (U : Set W) (hU : BruhatUpper cs U) (m : BottSamelsonModule cs (i::l))
    (hm : bottSetProjection cs (i::l) (simpleInter cs i U) m=0) :
    ∃ n : BottSamelsonModule cs l,
      (∀ x∈U, bottStalkProjection cs l x n=bottStalkProjection cs l x (bottHeadTail cs i l m)) ∧
      (∀ x∈simplePull cs i U,
        bottStalkProjection cs l x n=bottStalkProjection cs l x (bottHeadReflectedTail cs i l m).val) := by
  apply bottHeadPatch_lift cs i l H U hU m
  have hz := (bottHeadSet_zero_iff cs i l (simpleInter cs i U) m).mp hm
  intro x hx
  apply ((bottSetProjection_zero_iff cs l (simpleInter cs i U) _).mp hz.1 x hx).trans
  exact ((bottSetProjection_zero_iff cs l (simplePull cs i (simpleInter cs i U)) _).mp hz.2 x
    ((simpleInter_stable cs i U x).mpr hx)).symm

end
end KLInvariance.TitsSpace

end


section

namespace KLInvariance.TitsSpace
open Module CoordinateProjection ReflectionPairTranslation
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 theorem bottCommon_lift (i : I) (l : List I) (U : Set W)
    (z : bottCommonKernel cs i l U) :
    ∃ m : BottSamelsonModule cs (i::l),
      bottSetProjection cs (i::l) U m=z.val ∧
      bottSetProjection cs (i::l) (simpleInter cs i U) m=0 ∧
      bottSetProjection cs l U (bottHeadTail cs i l m)=0 := by
  let m : BottSamelsonModule cs (i::l) :=
    (bottSetProjection_surjective cs (i::l) U z.val).choose
  have hm : bottSetProjection cs (i::l) U m=z.val :=
    (bottSetProjection_surjective cs (i::l) U z.val).choose_spec
  refine ⟨m,hm,?_,?_⟩
  · exact (congrArg (bottInterRestriction cs i (i::l) U) hm).trans z.property.1
  · exact (bottSetFirst_project cs i l U m).symm.trans
      ((congrArg (bottSetFirst cs i l U) hm).trans z.property.2)

 theorem bottCommon_patch_lift (i : I) (l : List I) (H : BottFlabby cs l)
    (U : Set W) (hU : BruhatUpper cs U) (m : BottSamelsonModule cs (i::l))
    (hmJ : bottSetProjection cs (i::l) (simpleInter cs i U) m=0)
    (hmp : bottSetProjection cs l U (bottHeadTail cs i l m)=0) :
    ∃ n : BottSamelsonModule cs l, bottSetProjection cs l U n=0 ∧
      bottSetProjection cs l (simplePull cs i U) n=
      bottSetProjection cs l (simplePull cs i U) (bottHeadReflectedTail cs i l m).val := by
  let n : BottSamelsonModule cs l := (bottHeadPatch_lift_of_zero_inter cs i l H U hU m hmJ).choose
  have hnp := (bottHeadPatch_lift_of_zero_inter cs i l H U hU m hmJ).choose_spec.1
  have hnq := (bottHeadPatch_lift_of_zero_inter cs i l H U hU m hmJ).choose_spec.2
  refine ⟨n,?_,Subtype.ext (funext fun x => hnq x.val x.property)⟩
  apply (bottSetProjection_zero_iff cs l U n).mpr
  intro x hx
  exact (hnp x hx).trans ((bottSetProjection_zero_iff cs l U _).mp hmp x hx)

 theorem bottCommon_range_of_patch (i : I) (l : List I) (U : Set W)
    (z : bottCommonKernel cs i l U) (m : BottSamelsonModule cs (i::l))
    (hm : bottSetProjection cs (i::l) U m=z.val) (n : BottSamelsonModule cs l)
    (hnU : bottSetProjection cs l U n=0)
    (hnq : bottSetProjection cs l (simplePull cs i U) n=
      bottSetProjection cs l (simplePull cs i U) (bottHeadReflectedTail cs i l m).val) :
    ∃ d : Twist (coefficientAction cs (cs.simple i)).toRingEquiv
        (LinearMap.ker (bottUnionRestriction cs i l U)),
      bottCommonSecond cs i l U z=
        twistMap (coefficientAction cs (cs.simple i)).toRingEquiv (bottUnionKernelSecond cs i l U) d := by
  let d : LinearMap.ker (bottUnionRestriction cs i l U) :=
    ⟨bottSetProjection cs l (simpleUnion cs i U) n,hnU⟩
  refine ⟨Twist.mk d,?_⟩
  change bottSetSecond cs i l U z.val=Twist.mk (bottSetProjection cs l (simplePull cs i U) n)
  exact ((congrArg (bottSetSecond cs i l U) hm).symm.trans
    (bottSetSecond_project cs i l U m)).trans (congrArg Twist.mk hnq.symm)

 theorem bottCommon_range_of_lift (i : I) (l : List I) (H : BottFlabby cs l)
    (U : Set W) (hU : BruhatUpper cs U) (z : bottCommonKernel cs i l U)
    (m : BottSamelsonModule cs (i::l)) (hm : bottSetProjection cs (i::l) U m=z.val)
    (hmJ : bottSetProjection cs (i::l) (simpleInter cs i U) m=0)
    (hmp : bottSetProjection cs l U (bottHeadTail cs i l m)=0) :
    ∃ d : Twist (coefficientAction cs (cs.simple i)).toRingEquiv
        (LinearMap.ker (bottUnionRestriction cs i l U)),
      bottCommonSecond cs i l U z=
        twistMap (coefficientAction cs (cs.simple i)).toRingEquiv (bottUnionKernelSecond cs i l U) d := by
  exact bottCommon_range_of_patch cs i l U z m hm _
    (bottCommon_patch_lift cs i l H U hU m hmJ hmp).choose_spec.1
    (bottCommon_patch_lift cs i l H U hU m hmJ hmp).choose_spec.2

 theorem bottCommon_range_forward (i : I) (l : List I) (H : BottFlabby cs l)
    (U : Set W) (hU : BruhatUpper cs U) (z : bottCommonKernel cs i l U) :
    ∃ d : Twist (coefficientAction cs (cs.simple i)).toRingEquiv
        (LinearMap.ker (bottUnionRestriction cs i l U)),
      bottCommonSecond cs i l U z=
        twistMap (coefficientAction cs (cs.simple i)).toRingEquiv (bottUnionKernelSecond cs i l U) d :=
  bottCommon_range_of_lift cs i l H U hU z _ (bottCommon_lift cs i l U z).choose_spec.1
    (bottCommon_lift cs i l U z).choose_spec.2.1
    (bottCommon_lift cs i l U z).choose_spec.2.2

 theorem bottCommon_range_backward (i : I) (l : List I) (U : Set W)
    (d : Twist (coefficientAction cs (cs.simple i)).toRingEquiv
      (LinearMap.ker (bottUnionRestriction cs i l U))) :
    ∃ z : bottCommonKernel cs i l U,
      bottCommonSecond cs i l U z=
        twistMap (coefficientAction cs (cs.simple i)).toRingEquiv (bottUnionKernelSecond cs i l U) d := by
  let n : BottSamelsonModule cs l :=
    (bottSetProjection_surjective cs l (simpleUnion cs i U) d.val.val).choose
  have hn : bottSetProjection cs l (simpleUnion cs i U) n=d.val.val :=
    (bottSetProjection_surjective cs l (simpleUnion cs i U) d.val.val).choose_spec
  have hnU : bottSetProjection cs l U n=0 :=
    (congrArg (bottUnionRestriction cs i l U) hn).trans d.val.property
  let z : bottCommonKernel cs i l U :=
    ⟨bottSetProjection cs (i::l) U (bottSeed cs i l n),
      bottSeed_zero_inter cs i l U n hnU,(bottSetFirst_seed cs i l U n).trans hnU⟩
  refine ⟨z,?_⟩
  exact (bottSetSecond_seed cs i l U n).trans
    (congrArg Twist.mk (congrArg (bottUnionPullRestriction cs i l U) hn))

end
end KLInvariance.TitsSpace

end


section

/-! Projectivity on reflection-stable upper sets, via an ACTUAL tensor
splitting rather than an asserted reflexivity of a projected lattice. -/
namespace KLInvariance.TitsSpace
open Module CoordinateProjection ProjectiveRange ReflectionPairTranslation
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 theorem bottHeadLocalPair_eq_iff (i : I) (l : List I) (x : W)
    (m n : BottSamelsonModule cs (i::l)) :
    bottStalkProjection cs (i::l) x m=bottStalkProjection cs (i::l) x n ↔
      bottHeadLocalPair cs i l x m=bottHeadLocalPair cs i l x n :=
  maps_eq_iff_of_zero_iff _ _ (bottHeadLocalPair_zero_iff cs i l x) m n

 theorem bottTensorEnd_set_preserve (i : I) (l : List I) (U : Set W)
    (hU : ∀ x, cs.simple i*x∈U ↔ x∈U)
    (e : Module.End (SymmetricCoefficient (M := M)) (BottSamelsonModule cs l))
    (he : ∀ n x, x∈U → bottStalkProjection cs l x (e n)=bottStalkProjection cs l x n)
    (m : BottSamelsonModule cs (i::l)) :
    bottSetProjection cs (i::l) U (bottTensorEnd cs i l e m)=bottSetProjection cs (i::l) U m := by
  apply Subtype.ext
  funext x
  apply (bottHeadLocalPair_eq_iff cs i l x.val _ _).mpr
  apply (bottHeadLocalPair_value cs i l x.val _).trans
  apply Eq.trans ?_ (bottHeadLocalPair_value cs i l x.val m).symm
  apply Prod.ext
  · exact (congrArg (bottStalkProjection cs l x.val) (bottTensorEnd_first cs i l e m)).trans
      (he _ x.val x.property)
  · apply Twist.ext
    exact (congrArg (fun t => bottStalkProjection cs l (cs.simple i*x.val) t.val)
      (bottTensorEnd_second cs i l e m)).trans
      (he _ (cs.simple i*x.val) ((hU x.val).mpr x.property))

 theorem bottTensorEnd_set_kills (i : I) (l : List I) (U : Set W)
    (hU : ∀ x, cs.simple i*x∈U ↔ x∈U)
    (e : Module.End (SymmetricCoefficient (M := M)) (BottSamelsonModule cs l))
    (hz : ∀ n, bottSetProjection cs l U n=0 → e n=0)
    (m : BottSamelsonModule cs (i::l)) (hm : bottSetProjection cs (i::l) U m=0) :
    bottTensorEnd cs i l e m=0 := by
  have hmpq := (bottHeadSet_zero_iff cs i l U m).mp hm
  have hqzero : bottSetProjection cs l U (bottHeadReflectedTail cs i l m).val=0 := by
    apply (bottSetProjection_zero_iff cs l U _).mpr
    intro x hx
    exact (bottSetProjection_zero_iff cs l (simplePull cs i U) _).mp hmpq.2 x ((hU x).mpr hx)
  apply bottHead_components_injective cs i l
  · exact (bottTensorEnd_first cs i l e m).trans (hz _ hmpq.1)
  · apply Twist.ext
    exact (congrArg Twist.val (bottTensorEnd_second cs i l e m)).trans (hz _ hqzero)

 theorem bottStableUpper_projective (i : I) (l : List I) (U : Set W)
    (hU : ∀ x, cs.simple i*x∈U ↔ x∈U)
    [Module.Projective (SymmetricCoefficient (M := M)) (bottSetImage cs l U)] :
    Module.Projective (SymmetricCoefficient (M := M)) (bottSetImage cs (i::l) U) := by
  obtain ⟨s,hs⟩ := Module.projective_lifting_property (bottSetProjection cs l U)
    (LinearMap.id : bottSetImage cs l U →ₗ[SymmetricCoefficient (M := M)] bottSetImage cs l U)
    (bottSetProjection_surjective cs l U)
  have hs' : ∀ p, bottSetProjection cs l U (s p)=p := LinearMap.congr_fun hs
  let e := s.comp (bottSetProjection cs l U)
  have he : ∀ n x, x∈U → bottStalkProjection cs l x (e n)=bottStalkProjection cs l x n := by
    intro n x hx
    exact congrArg (fun z : bottSetImage cs l U => z.val ⟨x,hx⟩) (hs' (bottSetProjection cs l U n))
  have hz : ∀ n, bottSetProjection cs l U n=0 → e n=0 := by
    intro n hn
    exact (congrArg s hn).trans s.map_zero
  exact projective_of_end (bottSetProjection cs (i::l) U) (bottSetProjection_surjective cs (i::l) U)
    (bottTensorEnd cs i l e) (bottTensorEnd_set_preserve cs i l U hU e he)
    (bottTensorEnd_set_kills cs i l U hU e hz)

end
end KLInvariance.TitsSpace

end


section

namespace KLInvariance.ProjectiveRange
universe ur um uh up us
variable {R : Type ur} [CommRing R]
  {M : Type um} [AddCommGroup M] [Module R M]
  {H : Type uh} [AddCommGroup H] [Module R H]
  {P : Type up} [AddCommGroup P] [Module R P]
  {S : Type us} [AddCommGroup S] [Module R S]
  (r : M →ₗ[R] H) (f : M →ₗ[R] P) (k : P →ₗ[R] S)
  (h : ∀ m, r m=0 → k (f m)=0)
noncomputable section

 def onKernel : LinearMap.ker r →ₗ[R] LinearMap.ker k :=
  (f.comp (LinearMap.ker r).subtype).codRestrict (LinearMap.ker k) (fun m => h m.val m.property)

 def kernelOnKernelEquiv : ↥(LinearMap.ker r ⊓ LinearMap.ker f) ≃ₗ[R]
    LinearMap.ker (onKernel r f k h) where
  toFun z := ⟨⟨z.val,z.property.1⟩,Subtype.ext z.property.2⟩
  invFun z := ⟨z.val.val,z.val.property,congrArg Subtype.val z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

 theorem projective_of_two_stage (hr : Function.Surjective r)
    (hf : Function.Surjective (onKernel r f k h))
    [Module.Projective R H] [Module.Projective R (LinearMap.ker k)]
    [Module.Projective R ↥(LinearMap.ker r ⊓ LinearMap.ker f)] :
    Module.Projective R M := by
  let : Module.Projective R (LinearMap.ker (onKernel r f k h)) :=
    Module.Projective.of_equiv (kernelOnKernelEquiv r f k h)
  let : Module.Projective R (LinearMap.ker r) := projective_of_kernel (onKernel r f k h) hf
  exact projective_of_kernel r hr
end
end KLInvariance.ProjectiveRange

end


section

namespace KLInvariance.TitsSpace
open Module CoordinateProjection ReflectionPairTranslation ProjectiveRange
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 theorem bottInter_first_zero (i : I) (l : List I) (U : Set W)
    (z : bottSetImage cs (i::l) U) (hz : bottInterRestriction cs i (i::l) U z=0) :
    bottInterRestriction cs i l U (bottSetFirst cs i l U z)=0 :=
  (bottSetFirst_restrict cs i l (fun _ h => h.1) z).symm.trans
    ((congrArg (bottSetFirst cs i l (simpleInter cs i U)) hz).trans (map_zero _))

 theorem bottInterKernelFirst_surjective (i : I) (l : List I) (U : Set W) :
    Function.Surjective (onKernel (bottInterRestriction cs i (i::l) U) (bottSetFirst cs i l U)
      (bottInterRestriction cs i l U) (bottInter_first_zero cs i l U)) := by
  intro z
  let n : BottSamelsonModule cs l := (bottSetProjection_surjective cs l U z.val).choose
  have hn : bottSetProjection cs l U n=z.val := (bottSetProjection_surjective cs l U z.val).choose_spec
  have hnJ : bottSetProjection cs l (simpleInter cs i U) n=0 :=
    (congrArg (bottInterRestriction cs i l U) hn).trans z.property
  let w : LinearMap.ker (bottInterRestriction cs i (i::l) U) :=
    ⟨bottSetProjection cs (i::l) U (bottSeed cs i l n),
      bottSeed_zero_stable cs i l (simpleInter cs i U) (simpleInter_stable cs i U) n hnJ⟩
  exact ⟨w,Subtype.ext ((bottSetFirst_seed cs i l U n).trans hn)⟩

 theorem bottCommon_projective (i : I) (l : List I) (HP : BottProjectiveUpper cs l)
    (HF : BottFlabby cs l) (U : Set W) (hU : BruhatUpper cs U) :
    Module.Projective (SymmetricCoefficient (M := M)) (bottCommonKernel cs i l U) := by
  let : Module.Projective (SymmetricCoefficient (M := M)) (bottSetImage cs l U) := HP U hU
  let : Module.Projective (SymmetricCoefficient (M := M)) (bottSetImage cs l (simpleUnion cs i U)) :=
    HP (simpleUnion cs i U) (hU.simpleUnion cs U i)
  let : Module.Projective (SymmetricCoefficient (M := M)) (LinearMap.ker (bottUnionRestriction cs i l U)) :=
    kernel_projective (bottUnionRestriction cs i l U) (bottSetRestrict_surjective cs l (fun _ h => Or.inl h))
  let : Module.Projective (SymmetricCoefficient (M := M))
      (Twist (coefficientAction cs (cs.simple i)).toRingEquiv (LinearMap.ker (bottUnionRestriction cs i l U))) :=
    Twist.projective _
  exact projective_of_coordinates (bottCommonSecond cs i l U) (bottCommonSecond_injective cs i l U)
    (twistMap (coefficientAction cs (cs.simple i)).toRingEquiv (bottUnionKernelSecond cs i l U))
    (twistMap_injective _ _ (bottUnionKernelSecond_injective cs i l U))
    (bottCommon_range_forward cs i l HF U hU) (bottCommon_range_backward cs i l U)

 theorem bottProjectiveUpper_cons (i : I) (l : List I) (HP : BottProjectiveUpper cs l)
    (HF : BottFlabby cs l) : BottProjectiveUpper cs (i::l) := by
  intro U hU
  let : Module.Projective (SymmetricCoefficient (M := M)) (bottSetImage cs l U) := HP U hU
  let : Module.Projective (SymmetricCoefficient (M := M)) (bottSetImage cs l (simpleInter cs i U)) :=
    HP (simpleInter cs i U) (hU.simpleInter cs U i)
  let : Module.Projective (SymmetricCoefficient (M := M)) (bottSetImage cs (i::l) (simpleInter cs i U)) :=
    bottStableUpper_projective cs i l (simpleInter cs i U) (simpleInter_stable cs i U)
  let : Module.Projective (SymmetricCoefficient (M := M)) (LinearMap.ker (bottInterRestriction cs i l U)) :=
    kernel_projective (bottInterRestriction cs i l U) (bottSetRestrict_surjective cs l (fun _ h => h.1))
  let : Module.Projective (SymmetricCoefficient (M := M))
      ↥(LinearMap.ker (bottInterRestriction cs i (i::l) U) ⊓ LinearMap.ker (bottSetFirst cs i l U)) :=
    bottCommon_projective cs i l HP HF U hU
  exact projective_of_two_stage (bottInterRestriction cs i (i::l) U) (bottSetFirst cs i l U)
    (bottInterRestriction cs i l U) (bottInter_first_zero cs i l U)
    (bottSetRestrict_surjective cs (i::l) (fun _ h => h.1)) (bottInterKernelFirst_surjective cs i l U)

end
end KLInvariance.TitsSpace

end


section

/-! The codimension-one two-character distinction needed for integral
Bott--Samelson section realization. No BMP character or pairing is assumed. -/
namespace KLInvariance.Realization
open Module
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

 theorem orthogonal_eq_id_or_rootReflection
    (B : LinearMap.BilinForm ℝ V) (a : V) (ha : B a a=2)
    (g : V ≃ₗ[ℝ] V) (hg : ∀ v w, B (g v) (g w)=B v w)
    (hline : ∀ v, g v-v ∈ Submodule.span ℝ {a}) :
    g.toLinearMap=LinearMap.id ∨ ∀ v, g v=Module.preReflection a (B a) v := by
  obtain ⟨r,hr⟩ := Submodule.mem_span_singleton.mp (hline a)
  have hga : g a=(1+r) • a := by rw [add_smul,one_smul,hr]; module
  have hn := hg a a
  rw [hga] at hn
  simp only [map_smul,LinearMap.smul_apply,smul_eq_mul,ha] at hn
  have hr0 : r*(r+2)=0 := by nlinarith
  rcases mul_eq_zero.mp hr0 with hr | hr
  · left
    have hga' : g a=a := by simpa only [hr,add_zero,one_smul] using hga
    ext v
    obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp (hline v)
    have hgv : g v=v+c • a := by rw [hc]; module
    have h := hg a v
    rw [hga',hgv] at h
    simp only [map_add,map_smul,ha,smul_eq_mul] at h
    have hc0 : c=0 := by linarith
    change g v=v
    simpa only [hc0,zero_smul,add_zero] using hgv
  · right
    have hr' : r= -2 := by linarith
    have hga' : g a= -a := by simpa only [hr',show (1:ℝ)+ -2= -1 by norm_num,neg_one_smul] using hga
    intro v
    obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp (hline v)
    have hgv : g v=v+c • a := by rw [hc]; module
    have h := hg a v
    rw [hga',hgv] at h
    simp only [map_neg,LinearMap.neg_apply,map_add,map_smul,ha,smul_eq_mul] at h
    have hc' : c= -(B a v) := by linarith
    rw [hgv,hc',Module.preReflection_apply,neg_smul,sub_eq_add_neg]

end KLInvariance.Realization

end


section

/-! Exact root-prime character classes of the actual Coxeter polynomial
coefficient action. These are the two-vertex blocks needed in integral
section realization; they are not BMP or KL-character assumptions. -/
namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 theorem reflection_character_congruence_iff {t : W} {a : I → ℝ}
    (ha : Represents M cs t a) (x y : W) :
    (∀ p : SymmetricCoefficient (M := M),
      SymmetricAlgebra.ι ℝ (Extended M) (embed M a) ∣
        coefficientAction cs x p-coefficientAction cs y p) ↔
      x=y ∨ y=t*x := by
  constructor
  · intro hp
    let w := y*x⁻¹
    have hline (v : Extended M) :
        extendedAction M cs w v-v ∈ Submodule.span ℝ {embed M a} := by
      let p := (coefficientAction cs x).symm (SymmetricAlgebra.ι ℝ (Extended M) v)
      have hx : coefficientAction cs x p=SymmetricAlgebra.ι ℝ (Extended M) v :=
        AlgEquiv.apply_symm_apply _ _
      have hy : coefficientAction cs y p =
          coefficientAction cs w (SymmetricAlgebra.ι ℝ (Extended M) v) := by
        have h := coefficientAction_mul cs w x p
        rw [show w*x=y by dsimp [w]; group,hx] at h
        exact h
      have h := hp p
      rw [hx,hy,coefficientAction_ι,← map_sub] at h
      have hs := (EdgeAlgebra.symmetric_ι_dvd_iff (embed M a)
        (v-extendedAction M cs w v)).mp h
      simpa only [neg_sub,EdgeAlgebra.rootLine] using (EdgeAlgebra.rootLine (k := ℝ) (embed M a)).neg_mem hs
    have hnorm : extendedForm M (embed M a) (embed M a)=2 := by
      rw [(extendedForm_spec M).2.2]
      exact ha.isRoot.norm
    rcases Realization.orthogonal_eq_id_or_rootReflection
      (extendedForm M) (embed M a) hnorm (extendedAction M cs w)
      (extendedAction_preserves M cs w) hline with hid | href
    · left
      have hw : w=1 := by
        apply extendedAction_injective M cs
        apply LinearEquiv.ext
        intro v
        change extendedAction M cs w v=extendedAction M cs 1 v
        rw [map_one]
        change extendedAction M cs w v=v
        exact LinearMap.congr_fun hid v
      exact (mul_inv_eq_one.mp hw).symm
    · right
      have hw : w=t := by
        apply extendedAction_injective M cs
        apply LinearEquiv.ext
        intro v
        rw [ha.extendedAction_eq]
        exact href v
      exact mul_inv_eq_iff_eq_mul.mp hw
  · rintro (rfl | rfl)
    · intro p
      rw [sub_self]
      exact dvd_zero _
    · intro p
      rw [coefficientAction_mul]
      exact reflectionCoefficient_divisible cs ha (coefficientAction cs x p)

 theorem reflection_character_separates {t : W} {a : I → ℝ}
    (ha : Represents M cs t a) {x y : W} (hxy : x ≠ y) (ht : y ≠ t*x) :
    ∃ p : SymmetricCoefficient (M := M),
      ¬ SymmetricAlgebra.ι ℝ (Extended M) (embed M a) ∣
        coefficientAction cs x p-coefficientAction cs y p := by
  by_contra! h
  exact (reflection_character_congruence_iff cs ha x y).mp h |>.elim hxy ht

end
end KLInvariance.TitsSpace

end


section

/-! Every nontrivial prime-local congruence class of actual Coxeter
polynomial characters is a two-vertex reflection block. -/
namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 theorem isReflection_of_prime_character_congruence
    (p : SymmetricCoefficient (M := M)) (hp : Prime p)
    {x y : W} (hxy : x ≠ y)
    (hcon : ∀ a, p ∣ coefficientAction cs x a-coefficientAction cs y a) :
    cs.IsReflection (y*x⁻¹) := by
  let w := y*x⁻¹
  have hw : w ≠ 1 := by
    intro h
    exact hxy (mul_inv_eq_one.mp h).symm
  have hex : ∃ v : Extended M, extendedAction M cs w v-v ≠ 0 := by
    by_contra! h
    apply hw
    apply extendedAction_injective M cs
    apply LinearEquiv.ext
    intro v
    rw [map_one]
    exact sub_eq_zero.mp (h v)
  obtain ⟨v,hv⟩ := hex
  let d := extendedAction M cs w v-v
  have hd : d ≠ 0 := hv
  have hdiv (z : Extended M) : p ∣ SymmetricAlgebra.ι ℝ (Extended M)
      (extendedAction M cs w z-z) := by
    let a := (coefficientAction cs x).symm (SymmetricAlgebra.ι ℝ (Extended M) z)
    have hx : coefficientAction cs x a=SymmetricAlgebra.ι ℝ (Extended M) z :=
      AlgEquiv.apply_symm_apply _ _
    have hy : coefficientAction cs y a =
        coefficientAction cs w (SymmetricAlgebra.ι ℝ (Extended M) z) := by
      have h := coefficientAction_mul cs w x a
      rw [show w*x=y by dsimp [w]; group,hx] at h
      exact h
    have h := hcon a
    rw [hx,hy,coefficientAction_ι,← map_sub] at h
    simpa only [← map_neg,neg_sub] using dvd_neg.mpr h
  have hassoc := hp.associated_of_dvd (EdgeAlgebra.symmetric_ι_prime d hd) (hdiv v)
  have heq : LinearMap.range ((extendedAction M cs w).toLinearMap-LinearMap.id) =
      Submodule.span ℝ {d} := by
    apply le_antisymm
    · rintro z ⟨a,rfl⟩
      change extendedAction M cs w a-a ∈ Submodule.span ℝ {d}
      exact (EdgeAlgebra.symmetric_ι_dvd_iff d _).mp
        (dvd_trans hassoc.symm.dvd (hdiv a))
    · apply Submodule.span_le.mpr
      intro z hz
      rcases Set.mem_singleton_iff.mp hz with rfl
      exact ⟨v,rfl⟩
  apply isReflection_of_moving_rank_one M cs w
  rw [heq,finrank_span_singleton hd]

 theorem prime_character_class (p : SymmetricCoefficient (M := M)) (hp : Prime p)
    {x y : W} (hxy : x ≠ y)
    (hcon : ∀ a, p ∣ coefficientAction cs x a-coefficientAction cs y a) :
    ∃ t : W, cs.IsReflection t ∧ y=t*x ∧
      ∀ z, (∀ a, p ∣ coefficientAction cs x a-coefficientAction cs z a) ↔
        x=z ∨ z=t*x := by
  let t := y*x⁻¹
  have ht := isReflection_of_prime_character_congruence cs p hp hxy hcon
  let a := (positiveRoot M cs ⟨t,ht⟩).val
  have ha : Represents M cs t a := positiveRoot_represents M cs ⟨t,ht⟩
  have he : t*x=y := by dsimp [t]; group
  obtain ⟨c,hc⟩ := reflectionCoefficient_difference cs ha x
  rw [he] at hc
  have hpa : p ∣ SymmetricAlgebra.ι ℝ (Extended M) (embed M a) := hc ▸ hcon c
  have hane : embed M a ≠ 0 := by
    intro h
    have hn : extendedForm M (embed M a) (embed M a)=2 := by
      rw [(extendedForm_spec M).2.2]
      exact ha.isRoot.norm
    rw [h,map_zero] at hn
    norm_num at hn
  have hassoc := hp.associated_of_dvd (EdgeAlgebra.symmetric_ι_prime (embed M a) hane) hpa
  refine ⟨t,ht,he.symm,?_⟩
  intro z
  rw [← reflection_character_congruence_iff cs ha x z]
  exact forall_congr' fun c => ⟨fun h => dvd_trans hassoc.symm.dvd h,
    fun h => dvd_trans hassoc.dvd h⟩

end
end KLInvariance.TitsSpace

end


section

/-! Integral local projectors for finite character lattices. This lemma does
not assert any BMP character theorem or identify a chosen summand with BMP. -/
namespace KLInvariance.FiniteCharacterLocalization
universe u v w
variable {R : Type u} [CommRing R] {X : Type v}
  {E : X → Type w} [∀ x, AddCommGroup (E x)] [∀ x, Module R (E x)]
noncomputable section

 def diagonal (f : X → R) : (∀ x, E x) →ₗ[R] (∀ x, E x) where
  toFun m x := f x • m x
  map_add' := by intro m n; funext x; exact smul_add _ _ _
  map_smul' := by intro r m; funext x; exact smul_comm _ _ _

 def stabilizer (L : Submodule R (∀ x, E x)) : Subalgebra R (X → R) where
  carrier := {f | ∀ m ∈ L, diagonal f m ∈ L}
  mul_mem' := by
    intro f g hf hg m hm
    have h := hf _ (hg m hm)
    simpa only [diagonal,LinearMap.coe_mk,AddHom.coe_mk,Pi.mul_apply,mul_smul] using h
  one_mem' := by intro m hm; simpa [diagonal] using hm
  add_mem' := by
    intro f g hf hg m hm
    have he : diagonal (f+g) m = diagonal f m+diagonal g m := by
      funext x
      exact add_smul _ _ _
    rw [he]
    exact L.add_mem (hf m hm) (hg m hm)
  zero_mem' := by
    intro m _
    have he : diagonal (0 : X → R) m=0 := by
      funext x
      exact zero_smul _ _
    rw [he]
    exact L.zero_mem
  algebraMap_mem' := by
    intro r m hm
    exact L.smul_mem r hm

 theorem diagonal_mem {L : Submodule R (∀ x, E x)} {f : X → R}
    (hf : f ∈ stabilizer L) {m : ∀ x, E x} (hm : m ∈ L) :
    diagonal f m ∈ L := hf m hm

/-- A polynomial in stable diagonal weights which kills the complement of
`C` and is a common scalar on `C`. Its scalar is a product, not a quotient. -/
 theorem uniform_projector (L : Submodule R (∀ x, E x)) (C : Finset X)
    (f : X → R) (hf : f ∈ stabilizer L) (hz : ∀ x ∉ C, f x=0) :
    ∃ g ∈ stabilizer L,
      (∀ x ∈ C, g x=∏ y ∈ C, f y) ∧ (∀ x ∉ C, g x=0) := by
  classical
  let d : R := ∏ y ∈ C, f y
  let h : X → R := ∏ y ∈ C, (algebraMap R (X → R) (f y)-f)
  have hh : h ∈ stabilizer L := by
    exact (stabilizer L).prod_mem fun y _ =>
      (stabilizer L).sub_mem ((stabilizer L).algebraMap_mem (f y)) hf
  refine ⟨algebraMap R (X → R) d-h,
    (stabilizer L).sub_mem ((stabilizer L).algebraMap_mem d) hh,?_,?_⟩
  · intro x hx
    change d-h x=d
    suffices h x=0 by rw [this,sub_zero]
    dsimp [h]
    rw [Finset.prod_apply]
    apply Finset.prod_eq_zero hx
    simp
  · intro x hx
    change d-h x=0
    suffices h x=d by rw [this,sub_self]
    dsimp [h,d]
    rw [Finset.prod_apply]
    apply Finset.prod_congr rfl
    intro y _
    simp [hz x hx]

/-- Separate one residue-character class from its complement without
inverting any element of the coefficient domain. -/
 theorem class_projector [Fintype X] (L : Submodule R (∀ x, E x)) (p : R) (hp : Prime p)
    (C : Finset X) (x : X)
    (test : X → X → R) (htest : ∀ y, test y ∈ stabilizer L)
    (hzero : ∀ y ∉ C, test y y=0)
    (hunit : ∀ y ∉ C, ¬ p ∣ test y x)
    (hcongr : ∀ z ∈ C, ∀ y, p ∣ test y z-test y x) :
    ∃ d : R, ¬ p ∣ d ∧ ∃ g ∈ stabilizer L,
      (∀ z ∈ C, g z=d) ∧ (∀ z ∉ C, g z=0) := by
  classical
  let f : X → R := ∏ y ∈ Finset.univ \ C, test y
  have hf : f ∈ stabilizer L :=
    (stabilizer L).prod_mem fun y _ => htest y
  have hfu (z : X) (hz : z ∈ C) : ¬ p ∣ f z := by
    dsimp [f]
    rw [Finset.prod_apply]
    apply hp.not_dvd_finsetProd
    intro y hy
    have hyC := (Finset.mem_sdiff.mp hy).2
    intro h
    apply hunit y hyC
    simpa only [sub_sub_cancel] using dvd_sub h (hcongr z hz y)
  have hfz (z : X) (hz : z ∉ C) : f z=0 := by
    dsimp [f]
    rw [Finset.prod_apply]
    exact Finset.prod_eq_zero (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hz⟩) (hzero z hz)
  obtain ⟨g,hg,hgc,hgz⟩ := uniform_projector L C f hf hfz
  refine ⟨∏ z ∈ C, f z,?_,g,hg,hgc,hgz⟩
  exact hp.not_dvd_finsetProd (fun z hz => hfu z hz)

/-- Local lifts on each finite character block assemble after a single
scalar denominator away from the prime. -/
 theorem partition_local_denominator {Q : Type*} [Fintype Q]
    (L : Submodule R (∀ x, E x)) (p : R) (hp : Prime p) (q : X → Q)
    (z : ∀ x, E x) (d : Q → R) (hd : ∀ j, ¬ p ∣ d j)
    (g : Q → X → R) (hg : ∀ j, g j ∈ stabilizer L)
    (hgin : ∀ j x, q x=j → g j x=d j)
    (hgout : ∀ j x, q x≠j → g j x=0)
    (m : Q → ∀ x, E x) (hm : ∀ j, m j ∈ L)
    (hmatch : ∀ j x, q x=j → m j x=z x) :
    ∃ a : R, ¬ p ∣ a ∧ a • z ∈ L := by
  classical
  refine ⟨∏ j, d j,hp.not_dvd_finsetProd (fun j _ => hd j),?_⟩
  have hh : (∑ j : Q, (∏ k ∈ Finset.univ.erase j, d k) •
      diagonal (g j) (m j)) ∈ L := by
    exact L.sum_mem fun j _ => L.smul_mem _ (hg j _ (hm j))
  convert hh using 1
  funext x
  simp only [Pi.smul_apply,Finset.sum_apply]
  rw [Finset.sum_eq_single (q x)]
  · change (∏ j, d j) • z x = (∏ k ∈ Finset.univ.erase (q x),d k) •
      (g (q x) x • m (q x) x)
    rw [hgin _ _ rfl,hmatch _ _ rfl,← mul_smul,
      Finset.prod_erase_mul _ _ (Finset.mem_univ _)]
  · intro j _ hj
    change (∏ k ∈ Finset.univ.erase j,d k) • (g j x • m j x)=0
    rw [hgout j x (Ne.symm hj),zero_smul,smul_zero]
  · simp

 def residueSetoid {A : Type*} (p : R) (χ : A → X → R) : Setoid X where
  r x y := ∀ a, p ∣ χ a x-χ a y
  iseqv := ⟨fun x a => by rw [sub_self]; exact dvd_zero _,
    fun h a => by simpa only [neg_sub] using dvd_neg.mpr (h a),
    fun h h' a => by simpa only [sub_add_sub_cancel] using dvd_add (h a) (h' a)⟩

 theorem character_class_projector [Fintype X] {A : Type*}
    (L : Submodule R (∀ x, E x)) (p : R) (hp : Prime p)
    (χ : A → X → R) (hχ : ∀ a, χ a ∈ stabilizer L) (x : X) :
    ∃ d : R, ¬ p ∣ d ∧ ∃ g ∈ stabilizer L,
      (∀ z, (residueSetoid p χ).r x z → g z=d) ∧
      (∀ z, ¬ (residueSetoid p χ).r x z → g z=0) := by
  classical
  let C : Finset X := Finset.univ.filter ((residueSetoid p χ).r x)
  have hc (z : X) : z ∈ C ↔ (residueSetoid p χ).r x z := by simp [C]
  have ha : ∀ y : {y : X // y ∉ C}, ∃ a, ¬ p ∣ χ a x-χ a y.val := by
    intro y
    have hh : ¬ ∀ a, p ∣ χ a x-χ a y.val := fun h => y.property ((hc _).mpr h)
    exact not_forall.mp hh
  choose a ha using ha
  let test (y : X) : X → R := if hy : y ∉ C then
    χ (a ⟨y,hy⟩)-algebraMap R (X → R) (χ (a ⟨y,hy⟩) y) else 0
  have ht (y : X) : test y ∈ stabilizer L := by
    by_cases hy : y ∉ C
    · simp only [test,dite_eq_left hy]
      exact (stabilizer L).sub_mem (hχ _) ((stabilizer L).algebraMap_mem _)
    · simp only [test,dite_eq_right hy]
      exact (stabilizer L).zero_mem
  have hz (y : X) (hy : y ∉ C) : test y y=0 := by simp [test,hy]
  have hu (y : X) (hy : y ∉ C) : ¬ p ∣ test y x := by simpa [test,hy] using ha ⟨y,hy⟩
  have hcon (z : X) (hz : z ∈ C) (y : X) : p ∣ test y z-test y x := by
    by_cases hy : y ∉ C
    · simp only [test,dite_eq_left hy]
      change p ∣ (χ (a ⟨y,hy⟩) z-χ (a ⟨y,hy⟩) y)-
        (χ (a ⟨y,hy⟩) x-χ (a ⟨y,hy⟩) y)
      rw [sub_sub_sub_cancel_right]
      exact (residueSetoid p χ).symm ((hc z).mp hz) _
    · simp only [test,dite_eq_right hy,Pi.zero_apply,sub_self]
      exact dvd_zero _
  obtain ⟨d,hd,g,hg,hgc,hgz⟩ := class_projector L p hp C x test ht hz hu hcon
  exact ⟨d,hd,g,hg,fun z h => hgc z ((hc z).mpr h),
    fun z h => hgz z (fun hz => h ((hc z).mp hz))⟩

/-- Pair/blockwise liftability at a prime suffices for integral local
membership in a finite character-stable lattice. -/
 theorem character_local_denominator [Fintype X] {A : Type*}
    (L : Submodule R (∀ x, E x)) (p : R) (hp : Prime p)
    (χ : A → X → R) (hχ : ∀ a, χ a ∈ stabilizer L) (z : ∀ x, E x)
    (hlift : ∀ x, ∃ m ∈ L, ∀ y, (residueSetoid p χ).r x y → m y=z y) :
    ∃ a : R, ¬ p ∣ a ∧ a • z ∈ L := by
  classical
  let Q := Quotient (residueSetoid p χ)
  let : Fintype Q := Fintype.ofFinite Q
  let q : X → Q := Quotient.mk''
  have hq (j : Q) (y : X) : q y=j ↔ (residueSetoid p χ).r j.out y := by
    constructor
    · intro h
      exact (residueSetoid p χ).symm (Quotient.exact (h.trans (Quotient.out_eq j).symm))
    · intro h
      exact (Quotient.sound ((residueSetoid p χ).symm h)).trans (Quotient.out_eq j)
  have hproj (j : Q) := character_class_projector L p hp χ hχ j.out
  choose d hd g hg hgin hgout using hproj
  have hm (j : Q) := hlift j.out
  choose m hm hmatch using hm
  exact partition_local_denominator L p hp q z d hd g hg
    (fun j y h => hgin j y ((hq j y).mp h))
    (fun j y h => hgout j y (fun hh => h ((hq j y).mpr hh)))
    m hm (fun j y h => hmatch j y ((hq j y).mp h))

end
end KLInvariance.FiniteCharacterLocalization

end


section


namespace KLInvariance.ProjectiveLattice
variable {R : Type*} [CommRing R] [klPreservedInstance15 : IsDomain R] [klPreservedInstance16 : UniqueFactorizationMonoid R]

 omit [IsDomain R] [UniqueFactorizationMonoid R] in
 theorem finsupp_divide {ι : Type*} (r : R) (f : ι →₀ R)
    (h : ∀ i, r ∣ f i) : ∃ g : ι →₀ R, r • g = f := by
  classical
  let g : ι →₀ R := ∑ i ∈ f.support, Finsupp.single i (Classical.choose (h i))
  refine ⟨g, ?_⟩
  dsimp [g]
  rw [Finset.smul_sum]
  have heq : (∑ i ∈ f.support, r • Finsupp.single i (Classical.choose (h i))) =
      ∑ i ∈ f.support, Finsupp.single i (f i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finsupp.smul_single, smul_eq_mul, ← Classical.choose_spec (h i)]
  rw [heq]
  exact Finsupp.sum_single f

include klPreservedInstance15 klPreservedInstance16 in
 theorem prime_divide_of_relation {P : Type*} [AddCommGroup P] [Module R P]
    [Module.Projective R P] (p a c : R) (hp : Prime p) (ha : ¬p ∣ a)
    (m n : P) (h : a • m=(p*c) • n) : ∃ z : P, p • z=m := by
  have _ := klPreservedInstance15
  have _ := klPreservedInstance16
  obtain ⟨s,hs⟩ := Module.Projective.out (R := R) (P := P)
  have hdvd : ∀ i, p ∣ s m i := by
    intro i
    have he := congrArg (fun z : P => s z i) h
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at he
    have hm : p ∣ a*s m i := by
      rw [he]
      exact dvd_mul_of_dvd_left (dvd_mul_right p c) _
    exact (hp.dvd_mul.mp hm).resolve_left ha
  obtain ⟨z,hz⟩ := finsupp_divide p (s m) hdvd
  refine ⟨Finsupp.linearCombination R id z,?_⟩
  rw [← map_smul,hz,hs]

 theorem mem_of_prime_local_membership
    {E : Type*} [AddCommGroup E] [Module R E] [Module.IsTorsionFree R E]
    (M : Submodule R E) [Module.Projective R M] (x : E)
    (hgeneric : ∃ c : R, c ≠ 0 ∧ c • x ∈ M)
    (hlocal : ∀ p : R, Prime p → ∃ a : R, ¬p ∣ a ∧ a • x ∈ M) : x ∈ M := by
  obtain ⟨c,hcz,hcx⟩ := hgeneric
  suffices ∀ c : R, c≠0 → c • x ∈ M → x ∈ M from this c hcz hcx
  intro c
  induction c using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => simp
  | h₂ c hc =>
    intro _ hcx
    obtain ⟨u,rfl⟩ := hc
    simpa using M.smul_mem (↑u⁻¹ : R) hcx
  | h₃ c p hcz hp ih =>
    intro _ hpcx
    obtain ⟨a,hpa,hax⟩ := hlocal p hp
    let m : M := ⟨(p*c) • x,hpcx⟩
    let n : M := ⟨a • x,hax⟩
    have he : a • m=(p*c) • n := by
      apply Subtype.ext
      exact smul_comm a (p*c) x
    obtain ⟨z,hz⟩ := prime_divide_of_relation p a c hp hpa m n he
    have hcx : c • x=(z : E) := by
      apply smul_right_injective E hp.ne_zero
      have hv := congrArg Subtype.val hz
      change p • (z : E)=(p*c) • x at hv
      simpa only [mul_smul] using hv.symm
    exact ih hcz (hcx ▸ z.property)

end KLInvariance.ProjectiveLattice

end


section

/-! Prime-local realization on arbitrary upper coordinate sets. Projectivity
of the actual image is kept explicit here and discharged by word induction. -/
namespace KLInvariance.TitsSpace
open Module CoordinateProjection FiniteCharacterLocalization
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 theorem bottSet_scaled (l : List I) (U : Set W)
    (z : ∀ x : U, bottStalk cs l x.val) :
    bottCoordinateDenominator cs l • z ∈ bottSetImage cs l U := by
  classical
  let c (e : BottIndex l) : SymmetricCoefficient (M := M) :=
    if h : bottWeight cs l e∈U then (z ⟨bottWeight cs l e,h⟩).val ⟨e,rfl⟩ else 0
  obtain ⟨m,hm⟩ := bottEvaluation_contains_scaled_coordinates cs l c
  refine ⟨m,?_⟩
  funext x
  apply Subtype.ext
  funext e
  rcases x with ⟨x,hx⟩
  rcases e with ⟨e,he⟩
  change bottWeight cs l e=x at he
  subst x
  change bottEvaluation cs l e m=bottCoordinateDenominator cs l * (z ⟨bottWeight cs l e,hx⟩).val ⟨e,rfl⟩
  simpa only [c,dite_eq_left hx] using hm e

 theorem BottCompatible.reflection_lift {l : List I} {U : Set W}
    {z : ∀ x : U, bottStalk cs l x.val} (hz : BottCompatible cs l U z)
    (x y : U) (t : W) (ht : cs.IsReflection t) (he : t*x.val=y.val) :
    ∃ m : BottSamelsonModule cs l,
      bottStalkProjection cs l x.val m=z x ∧ bottStalkProjection cs l y.val m=z y := by
  have he' : t*y.val=x.val := by rw [← he,← mul_assoc,ht.mul_self,one_mul]
  have hne : cs.length y.val ≠ cs.length x.val := by
    rw [← he]
    exact ht.length_mul_right_ne x.val
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · obtain ⟨m,hm,hn⟩ := hz y.val x.val y.property x.property ⟨hlt,t,ht,he'.symm⟩
    exact ⟨m,hn,hm⟩
  · exact hz x.val y.val x.property y.property ⟨hlt,t,ht,he.symm⟩

 theorem BottCompatible.prime_lift {l : List I} {U : Set W}
    {z : ∀ x : U, bottStalk cs l x.val} (hz : BottCompatible cs l U z)
    (p : SymmetricCoefficient (M := M)) (hp : Prime p) (x : U) :
    ∃ m : BottSamelsonModule cs l, ∀ y : U,
      (∀ a, p ∣ coefficientAction cs x.val a-coefficientAction cs y.val a) →
      bottStalkProjection cs l y.val m=z y := by
  classical
  by_cases hx : ∃ y : U, x≠y ∧
      ∀ a, p ∣ coefficientAction cs x.val a-coefficientAction cs y.val a
  · obtain ⟨y,hxy,hcon⟩ := hx
    obtain ⟨t,ht,he,hclass⟩ := prime_character_class cs p hp
      (fun h => hxy (Subtype.ext h)) hcon
    obtain ⟨m,hm,hn⟩ := hz.reflection_lift cs x y t ht he.symm
    refine ⟨m,?_⟩
    intro w hw
    rcases (hclass w.val).mp hw with hxw | hwy
    · have h : w=x := Subtype.ext hxw.symm
      subst w
      exact hm
    · have h : w=y := Subtype.ext (hwy.trans he.symm)
      subst w
      exact hn
  · obtain ⟨m,hm⟩ := bottStalkProjection_surjective cs l x.val (z x)
    refine ⟨m,?_⟩
    intro y hy
    have h : y=x := by
      by_contra h
      exact hx ⟨y,Ne.symm h,hy⟩
    subst y
    exact hm

 def BottUpperIndex (l : List I) (U : Set W) := {e : BottIndex l // bottWeight cs l e∈U}

 def bottIndexSetEval (l : List I) (U : Set W) : BottSamelsonModule cs l →ₗ[
    SymmetricCoefficient (M := M)]
    (∀ e : BottUpperIndex cs l U, bottStalk cs l (bottWeight cs l e.val)) :=
  LinearMap.pi (fun e => bottStalkProjection cs l (bottWeight cs l e.val))

 theorem bottIndexSetEval_stable (l : List I) (U : Set W)
    (a : SymmetricCoefficient (M := M)) :
    (fun e : BottUpperIndex cs l U => coefficientAction cs (bottWeight cs l e.val) a) ∈
      stabilizer (LinearMap.range (bottIndexSetEval cs l U)) := by
  rintro z ⟨m,rfl⟩
  refine ⟨bottSamelsonRight cs l a m,?_⟩
  funext e
  exact bottStalkProjection_right cs l _ a m

 theorem BottCompatible.local_denominator {l : List I} {U : Set W}
    {z : ∀ x : U, bottStalk cs l x.val} (hz : BottCompatible cs l U z)
    (p : SymmetricCoefficient (M := M)) (hp : Prime p) :
    ∃ a : SymmetricCoefficient (M := M), ¬p ∣ a ∧ a • z∈bottSetImage cs l U := by
  classical
  let : Fintype (BottUpperIndex cs l U) := inferInstanceAs (Fintype {e : BottIndex l // bottWeight cs l e∈U})
  let zz : ∀ e : BottUpperIndex cs l U, bottStalk cs l (bottWeight cs l e.val) :=
    fun e => z ⟨bottWeight cs l e.val,e.property⟩
  have hlift : ∀ e : BottUpperIndex cs l U, ∃ m ∈ LinearMap.range (bottIndexSetEval cs l U),
      ∀ f, (residueSetoid p (fun a e => coefficientAction cs (bottWeight cs l e.val) a)).r e f → m f=zz f := by
    intro e
    obtain ⟨m,hm⟩ := hz.prime_lift cs p hp ⟨bottWeight cs l e.val,e.property⟩
    exact ⟨bottIndexSetEval cs l U m,⟨m,rfl⟩,fun f hf => hm ⟨bottWeight cs l f.val,f.property⟩ hf⟩
  obtain ⟨a,ha,m,hm⟩ := character_local_denominator
    (LinearMap.range (bottIndexSetEval cs l U)) p hp
    (fun a e => coefficientAction cs (bottWeight cs l e.val) a)
    (bottIndexSetEval_stable cs l U) zz hlift
  refine ⟨a,ha,m,?_⟩
  funext x
  apply Subtype.ext
  funext e
  rcases x with ⟨x,hx⟩
  rcases e with ⟨e,he⟩
  change bottWeight cs l e=x at he
  subst x
  have hh := congrArg (fun q => (q ⟨e,hx⟩).val ⟨e,rfl⟩) hm
  exact hh

 theorem bottFlabby_of_projective (l : List I) (H : BottProjectiveUpper cs l) :
    BottFlabby cs l := by
  intro U hU z hz
  let : Module.Projective (SymmetricCoefficient (M := M)) (bottSetImage cs l U) := H U hU
  let : UniqueFactorizationMonoid (SymmetricCoefficient (M := M)) :=
    (SymmetricAlgebra.equivMvPolynomial (Module.Free.chooseBasis ℝ (Extended M))).symm.toRingEquiv.toMulEquiv.uniqueFactorizationMonoid inferInstance
  exact ProjectiveLattice.mem_of_prime_local_membership (bottSetImage cs l U) z
    ⟨bottCoordinateDenominator cs l,bottCoordinateDenominator_ne_zero cs l,bottSet_scaled cs l U z⟩
    (hz.local_denominator cs)

end
end KLInvariance.TitsSpace

end


section

/-! Unconditional flabbiness of the actual integral tensor-word projection
sheaf, obtained from projectivity of every upper-coordinate image. -/
namespace KLInvariance.TitsSpace
open Module CoordinateProjection
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 theorem bottSetProjection_nil_injective (U : Set W) (hU : (1 : W)∈U) :
    Function.Injective (bottSetProjection cs [] U) := by
  intro m n h
  apply bottEvaluation_injective cs []
  funext e
  exact congrArg (fun z : bottSetImage cs [] U => (z.val ⟨1,hU⟩).val ⟨e,rfl⟩) h

 theorem bottSetImage_nil_subsingleton (U : Set W) (hU : (1 : W)∉U) :
    Subsingleton (bottSetImage cs [] U) := by
  constructor
  intro p q
  apply Subtype.ext
  funext x
  have hx : x.val≠1 := fun h => hU (h ▸ x.property)
  let := bottStalk_nil_subsingleton cs x.val hx
  exact Subsingleton.elim _ _

 theorem bottSetImage_nil_projective (U : Set W) :
    Module.Projective (SymmetricCoefficient (M := M)) (bottSetImage cs [] U) := by
  by_cases hU : (1 : W)∈U
  · exact Module.Projective.of_equiv (LinearEquiv.ofBijective (bottSetProjection cs [] U)
      ⟨bottSetProjection_nil_injective cs U hU,bottSetProjection_surjective cs [] U⟩)
  · let := bottSetImage_nil_subsingleton cs U hU
    infer_instance

 theorem bottProjectiveUpper (l : List I) : BottProjectiveUpper cs l := by
  induction l with
  | nil => exact fun U _ => bottSetImage_nil_projective cs U
  | cons i l ih => exact bottProjectiveUpper_cons cs i l ih (bottFlabby_of_projective cs l ih)

 theorem bottFlabby (l : List I) : BottFlabby cs l :=
  bottFlabby_of_projective cs l (bottProjectiveUpper cs l)

end
end KLInvariance.TitsSpace

end


section

/-! Flabbiness of the genuine interval word sheaf; the extension outside the
finite support is zero, not an extra assumption on the source interval. -/
namespace KLInvariance.TitsSpace
open Module MomentGraph BruhatGraph
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 theorem bottStalk_subsingleton_of_not_bruhat (l : List I) (hl : cs.IsReduced l)
    (x : W) (hx : ¬BruhatLE cs x (cs.wordProd l)) : Subsingleton (bottStalk cs l x) := by
  constructor
  intro p q
  apply Subtype.ext
  funext e
  exact (hx (e.property ▸ bottWeight_bruhat cs l hl e.val)).elim

 def intervalUpperClosure (b : W) (U : Set (Interval cs 1 b)) : Set W :=
  {x | ∃ a : Interval cs 1 b, a∈U ∧ BruhatLE cs a.val x}

 omit [Fintype I] in
 theorem intervalUpperClosure_upper (b : W) (U : Set (Interval cs 1 b)) :
    BruhatUpper cs (intervalUpperClosure cs b U) := by
  rintro x y hxy ⟨a,ha,hax⟩
  exact ⟨a,ha,bruhat_trans cs hax hxy⟩

 omit [Fintype I] in
 theorem intervalUpperClosure_member (b : W) (U : Set (Interval cs 1 b)) (hU : IsUpperSet U)
    (x : W) (hx : x∈intervalUpperClosure cs b U) (hxb : BruhatLE cs x b) :
    (⟨x,one_bruhat cs x,hxb⟩ : Interval cs 1 b)∈U := by
  obtain ⟨a,ha,hax⟩ := hx
  exact hU hax ha

 def bottIntervalExtension (l : List I) (U : Set (Interval cs 1 (cs.wordProd l)))
    (f : (bottProjectionSheaf cs l 1 (cs.wordProd l)).Assignment)
    (x : intervalUpperClosure cs (cs.wordProd l) U) : bottStalk cs l x.val := by
  classical
  exact if h : BruhatLE cs x.val (cs.wordProd l) then f ⟨x.val,one_bruhat cs x.val,h⟩ else 0

 theorem bottIntervalExtension_apply (l : List I) (U : Set (Interval cs 1 (cs.wordProd l)))
    (f : (bottProjectionSheaf cs l 1 (cs.wordProd l)).Assignment)
    (x : Interval cs 1 (cs.wordProd l)) (hx : x.val∈intervalUpperClosure cs (cs.wordProd l) U) :
    bottIntervalExtension cs l U f ⟨x.val,hx⟩=f x := by
  classical
  dsimp only [bottIntervalExtension]
  exact dite_eq_left x.property.2

 theorem bottIntervalExtension_compatible (l : List I) (hl : cs.IsReduced l)
    (U : Set (Interval cs 1 (cs.wordProd l))) (hU : IsUpperSet U)
    (f : (bottProjectionSheaf cs l 1 (cs.wordProd l)).Assignment)
    (hf : (bottProjectionSheaf cs l 1 (cs.wordProd l)).CompatibleOn U f) :
    BottCompatible cs l (intervalUpperClosure cs (cs.wordProd l) U) (bottIntervalExtension cs l U f) := by
  intro x y hx hy hxy
  by_cases hyb : BruhatLE cs y (cs.wordProd l)
  · have hxb : BruhatLE cs x (cs.wordProd l) := bruhat_trans cs (.single hxy) hyb
    let xx : Interval cs 1 (cs.wordProd l) := ⟨x,one_bruhat cs x,hxb⟩
    let yy : Interval cs 1 (cs.wordProd l) := ⟨y,one_bruhat cs y,hyb⟩
    let e : Edge cs 1 (cs.wordProd l) := ⟨(xx,yy),hxy⟩
    have hh := hf e (intervalUpperClosure_member cs _ U hU x hx hxb)
      (intervalUpperClosure_member cs _ U hU y hy hyb)
    obtain ⟨m,hm,hn⟩ := (PairProjection.compatible_iff _ _ _ _).mp hh
    exact ⟨m,hm.trans (bottIntervalExtension_apply cs l U f xx hx).symm,
      hn.trans (bottIntervalExtension_apply cs l U f yy hy).symm⟩
  · let := bottStalk_subsingleton_of_not_bruhat cs l hl y hyb
    obtain ⟨m,hm⟩ := bottStalkProjection_surjective cs l x (bottIntervalExtension cs l U f ⟨x,hx⟩)
    exact ⟨m,hm,Subsingleton.elim _ _⟩

 theorem bottProjectionSheaf_flabby (l : List I) (hl : cs.IsReduced l) :
    (bottProjectionSheaf cs l 1 (cs.wordProd l)).Flabby := by
  intro U hU f hf
  obtain ⟨m,hm⟩ := bottFlabby cs l _ (intervalUpperClosure_upper cs _ U)
    (bottIntervalExtension cs l U f) (bottIntervalExtension_compatible cs l hl U hU f hf)
  refine ⟨(bottSection cs l 1 (cs.wordProd l) m).val,(bottSection cs l 1 (cs.wordProd l) m).property,?_⟩
  intro x hx
  exact (congrFun hm ⟨x.val,x,hx,bruhat_refl cs x.val⟩).trans
    (bottIntervalExtension_apply cs l U f x ⟨x,hx,bruhat_refl cs x.val⟩)

end
end KLInvariance.TitsSpace

end


section

/-! Integral adjoints, not restrictions of a form to arbitrary summands.
This is used to transport a genuine BMP projector through the word duality. -/
namespace PerfectAdjoint
open Module
universe ur um
variable {R : Type ur} [CommRing R]
  {M : Type um} [AddCommGroup M] [Module R M]
  (d : M ≃ₗ[R] Dual R M)
noncomputable section

 def adjoint (f : End R M) : End R M :=
  d.symm.toLinearMap.comp (f.dualMap.comp d.toLinearMap)

 theorem pairing (f : End R M) (m n : M) : d (adjoint d f m) n=d m (f n) := by
  change d (d.symm (f.dualMap (d m))) n=d m (f n)
  rw [LinearEquiv.apply_symm_apply]
  rfl

 theorem adjoint_comp (f g : End R M) : adjoint d (f.comp g)=(adjoint d g).comp (adjoint d f) := by
  apply LinearMap.ext
  intro m
  apply d.injective
  apply LinearMap.ext
  intro n
  rw [pairing]
  change d m (f (g n))=d (adjoint d g (adjoint d f m)) n
  rw [pairing,pairing]

 theorem adjoint_idempotent (f : End R M) (hf : ∀ m, f (f m)=f m) (m : M) :
    adjoint d f (adjoint d f m)=adjoint d f m := by
  apply d.injective
  apply LinearMap.ext
  intro n
  rw [pairing,pairing,hf,pairing]

 theorem commutes_of_balanced (f t : End R M)
    (ht : ∀ m n, d (t m) n=d m (t n)) (hf : ∀ m, f (t m)=t (f m)) (m : M) :
    adjoint d f (t m)=t (adjoint d f m) := by
  apply d.injective
  apply LinearMap.ext
  intro n
  rw [pairing,ht,ht,pairing,hf]

 theorem symmetric_pairing (hsym : ∀ m n, d m n=d n m)
    (f : End R M) (m n : M) : d m (adjoint d f n)=d (f m) n := by
  rw [hsym,pairing,hsym]

 theorem adjoint_adjoint (hsym : ∀ m n, d m n=d n m) (f : End R M) :
    adjoint d (adjoint d f)=f := by
  apply LinearMap.ext
  intro m
  apply d.injective
  apply LinearMap.ext
  intro n
  rw [pairing,symmetric_pairing d hsym]

end
end PerfectAdjoint

end


section


namespace KLInvariance.Graded
open Module
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {M : Type um} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
  (𝓐 : ℤ → Submodule k A) (𝓜 : ℤ → Submodule k M)
  [DirectSum.Decomposition 𝓐] [DirectSum.Decomposition 𝓜]
noncomputable section

omit [IsScalarTower k A M] in
 theorem perfect_inverse_of_homogeneous_functional
    (p : M ≃ₗ[A] Dual A M) (l : ℤ)
    (hp : ∀ i j (m n : M), m ∈ 𝓜 i → n ∈ 𝓜 j → p m n ∈ 𝓐 (i+j-l))
    (r : ℤ) (lam : Dual A M)
    (hlam : ∀ j (n : M), n ∈ 𝓜 j → lam n ∈ 𝓐 (j+r)) :
    p.symm lam ∈ 𝓜 (r+l) := by
  have hc : component 𝓜 (r+l) (p.symm lam) = p.symm lam := by
    apply p.injective
    apply LinearMap.ext
    intro y
    refine DirectSum.Decomposition.inductionOn 𝓜 ?_ ?_ ?_ y
    · simp
    · intro j v
      let f : M →ₗ[A] A :=
        { toFun := fun w => p w (v : M)
          map_add' := by intros; simp
          map_smul' := by intros; simp }
      have hh : ∀ i w, w ∈ 𝓜 i → f w ∈ 𝓐 (i+(j-l)) := by
        intro i w hw
        simpa only [f,LinearMap.coe_mk,AddHom.coe_mk,add_sub_assoc] using hp i j w v hw v.property
      have he := map_component 𝓜 𝓐 f (j-l) hh (j+r) (p.symm lam)
      have hi : j+r-(j-l)=r+l := by omega
      rw [hi] at he
      have hf : f (p.symm lam)=lam v := by
        dsimp only [f,LinearMap.coe_mk,AddHom.coe_mk]
        rw [LinearEquiv.apply_symm_apply]
      rw [hf] at he
      have hsame : component 𝓐 (j+r) (lam v)=lam v :=
        DirectSum.decompose_of_mem_same 𝓐 (hlam j v v.property)
      rw [hsame] at he
      change f (component 𝓜 (r+l) (p.symm lam)) = p (p.symm lam) v
      rw [LinearEquiv.apply_symm_apply]
      exact he.symm
    · intro x y hx hy
      simp only [map_add,hx,hy]
  rw [← hc]
  exact (DirectSum.decompose 𝓜 (p.symm lam) (r+l)).property

end
end KLInvariance.Graded

end


section

namespace KLInvariance.Graded
open Module
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {M : Type um} [AddCommGroup M] [Module k M] [Module A M]
  (𝓐 : ℤ → Submodule k A) (𝓜 : ℤ → Submodule k M)
  [DirectSum.Decomposition 𝓐] [DirectSum.Decomposition 𝓜]
noncomputable section

 theorem adjoint_homogeneous
    (p : M ≃ₗ[A] Dual A M) (l : ℤ)
    (hp : ∀ i j (m n : M), m ∈ 𝓜 i → n ∈ 𝓜 j → p m n ∈ 𝓐 (i+j-l))
    (f : End A M) (hf : ∀ n m, m ∈ 𝓜 n → f m ∈ 𝓜 n)
    (n : ℤ) (m : M) (hm : m ∈ 𝓜 n) : PerfectAdjoint.adjoint p f m ∈ 𝓜 n := by
  have h := perfect_inverse_of_homogeneous_functional 𝓐 𝓜 p l hp (n-l)
    (f.dualMap (p m)) (by
      intro j v hv
      have hv' := hp n j m (f v) hm (hf j v hv)
      have he : n+j-l=j+(n-l) := by omega
      change p m (f v) ∈ 𝓐 (j+(n-l))
      rw [← he]
      exact hv')
  simpa only [sub_add_cancel,PerfectAdjoint.adjoint,LinearMap.comp_apply,LinearEquiv.coe_coe] using h

end
end KLInvariance.Graded

end


section


end

end OAI
