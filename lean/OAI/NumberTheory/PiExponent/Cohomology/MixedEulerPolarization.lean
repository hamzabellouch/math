import OAI.NumberTheory.PiExponent.Cohomology.MixedEulerAlgebra

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

def structureLineBundle (X : Scheme.{0}) : LineBundle X where
  sheaf := structureSheaf X
  locallyRankOne _x :=
    ⟨⊤, trivial, ⟨Scheme.Modules.restrictUnitIso (⊤ : X.Opens).ι⟩⟩

def MixedDegreeLE (d : ℕ) (f : LineBundle X → ℤ) : Prop :=
  ∀ ls : List (LineBundle X), ls.length = d+1 → mixedDifference ls f = 0

theorem mixedDifference_perm {ls ks : List (LineBundle X)} (h : ls.Perm ks)
    (f : LineBundle X → ℤ) (hf : LineIsoInvariant f) :
    mixedDifference ls f = mixedDifference ks f := by
  induction h with
  | nil => rfl
  | cons L h ih => exact congrArg (tensorDifference L) ih
  | swap A B ls => exact tensorDifference_commute B A _ (hf.mixedDifference ls)
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

theorem mixedDifference_iso_cons (A B : LineBundle X) (e : A.sheaf ≅ B.sheaf)
    (ls : List (LineBundle X)) (f : LineBundle X → ℤ) (hf : LineIsoInvariant f) :
    mixedDifference (A :: ls) f = mixedDifference (B :: ls) f := by
  funext M
  change mixedDifference ls f (A.tensor M) - mixedDifference ls f M =
    mixedDifference ls f (B.tensor M) - mixedDifference ls f M
  rw [(hf.mixedDifference ls) (A.tensor M) (B.tensor M)
    (moduleTensorIso e (Iso.refl M.sheaf))]

theorem MixedDegreeLE.eq_zero_of_length_lt {d : ℕ} {f : LineBundle X → ℤ}
    (hf : MixedDegreeLE d f) (ls : List (LineBundle X)) (hlen : d < ls.length) :
    mixedDifference ls f = 0 := by
  have ht : (ls.take (ls.length - (d+1))).length + (d+1) = ls.length := by
    rw [List.length_take, Nat.min_eq_left (Nat.sub_le _ _)]
    omega
  have hd : (ls.drop (ls.length - (d+1))).length = d+1 := by
    rw [List.length_drop]
    omega
  rw [← List.take_append_drop (ls.length - (d+1)) ls, mixedDifference_append, hf _ hd,
    mixedDifference_zero]

theorem mixedDifference_tensor_base_of_degree {d : ℕ} {f : LineBundle X → ℤ}
    (hf : MixedDegreeLE d f) (ls : List (LineBundle X)) (hlen : ls.length = d)
    (A M : LineBundle X) :
    mixedDifference ls f (A.tensor M) = mixedDifference ls f M := by
  have hz := congrFun (hf (A :: ls) (by simp [hlen])) M
  exact sub_eq_zero.mp hz

theorem mixedDifference_eq_structure_of_degree {d : ℕ} {f : LineBundle X → ℤ}
    (hf : LineIsoInvariant f) (hdegree : MixedDegreeLE d f)
    (ls : List (LineBundle X)) (hlen : ls.length = d) (M : LineBundle X) :
    mixedDifference ls f M = mixedDifference ls f (structureLineBundle X) := by
  have he := (hf.mixedDifference ls) (M.tensor (structureLineBundle X)) M
    (moduleTensorRightUnit M.sheaf)
  exact he.symm.trans
    (mixedDifference_tensor_base_of_degree hdegree ls hlen M (structureLineBundle X))

theorem mixedDifference_tensor_cons_of_degree {d : ℕ} {f : LineBundle X → ℤ}
    (hf : LineIsoInvariant f) (hdegree : MixedDegreeLE d f)
    (A B : LineBundle X) (ls : List (LineBundle X)) (hlen : ls.length + 1 = d) :
    mixedDifference (A.tensor B :: ls) f =
      mixedDifference (A :: ls) f + mixedDifference (B :: ls) f := by
  apply mixedDifference_tensor_cons_of_next_eq_zero A B ls f hf
  apply hdegree
  simp only [List.length_cons]
  omega

theorem mixedDifference_pow_zero_cons (L : LineBundle X) (ls : List (LineBundle X))
    (f : LineBundle X → ℤ) (hf : LineIsoInvariant f) :
    mixedDifference (L.pow 0 :: ls) f = 0 := by
  funext M
  change mixedDifference ls f ((L.pow 0).tensor M) - mixedDifference ls f M = 0
  rw [(hf.mixedDifference ls) ((L.pow 0).tensor M) M (moduleTensorUnit M.sheaf)]
  exact sub_self _

theorem mixedDifference_pow_cons_of_degree {d : ℕ} {f : LineBundle X → ℤ}
    (hf : LineIsoInvariant f) (hdegree : MixedDegreeLE d f)
    (L : LineBundle X) (n : ℕ) (ls : List (LineBundle X)) (hlen : ls.length + 1 = d) :
    mixedDifference (L.pow n :: ls) f = n • mixedDifference (L :: ls) f := by
  induction n with
  | zero => simpa only [zero_nsmul] using mixedDifference_pow_zero_cons L ls f hf
  | succ n ih =>
      rw [mixedDifference_iso_cons (L.pow (n+1)) (L.tensor (L.pow n)) (Iso.refl _) ls f hf,
        mixedDifference_tensor_cons_of_degree hf hdegree L (L.pow n) ls hlen, ih]
      rw [add_comm, succ_nsmul]

theorem mixedDifference_replicate_pow (L : LineBundle X) (f : LineBundle X → ℤ)
    (hf : LineIsoInvariant f) (k n : ℕ) :
    mixedDifference (List.replicate k L) f (L.pow n) =
      (fwdDiff (1 : ℕ))^[k] (fun j => f (L.pow j)) n := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
      rw [List.replicate_succ]
      change mixedDifference (List.replicate k L) f (L.tensor (L.pow n)) -
        mixedDifference (List.replicate k L) f (L.pow n) = _
      rw [(hf.mixedDifference _) (L.tensor (L.pow n)) (L.pow (n+1)) (Iso.refl _), ih, ih]
      rw [Function.iterate_succ_apply']
      rfl

def mixedTop (f : LineBundle X → ℤ) (ls : List (LineBundle X)) : ℤ :=
  mixedDifference ls f (structureLineBundle X)

theorem mixedTop_replicate (L : LineBundle X) (f : LineBundle X → ℤ)
    (hf : LineIsoInvariant f) (d : ℕ) :
    mixedTop f (List.replicate d L) =
      (fwdDiff (1 : ℕ))^[d] (fun n => f (L.pow n)) 0 := by
  rw [mixedTop, (hf.mixedDifference _) (structureLineBundle X) (L.pow 0) (Iso.refl _)]
  exact mixedDifference_replicate_pow L f hf d 0

theorem mixedDifference_replicate_tensor_append {d : ℕ} {f : LineBundle X → ℤ}
    (hf : LineIsoInvariant f) (hdegree : MixedDegreeLE d f)
    (A B : LineBundle X) (n : ℕ) (ls : List (LineBundle X))
    (hlen : n + ls.length = d) :
    mixedDifference (List.replicate n (A.tensor B) ++ ls) f =
      ∑ k ∈ Finset.range (n+1), n.choose k •
        mixedDifference (List.replicate k A ++ List.replicate (n-k) B ++ ls) f := by
  induction n generalizing ls with
  | zero => simp
  | succ n ih =>
      have hm (L : LineBundle X) :
          mixedDifference (L :: (List.replicate n (A.tensor B) ++ ls)) f =
            mixedDifference (List.replicate n (A.tensor B) ++ L :: ls) f :=
        mixedDifference_perm List.perm_middle.symm f hf
      rw [List.replicate_succ, List.cons_append,
        mixedDifference_tensor_cons_of_degree hf hdegree A B _ (by
          simp only [List.length_append, List.length_replicate]; omega), hm A, hm B,
        ih (A :: ls) (by simp only [List.length_cons]; omega),
        ih (B :: ls) (by simp only [List.length_cons]; omega)]
      rw [Finset.sum_choose_succ_nsmul
        (fun a b => mixedDifference (List.replicate a A ++ List.replicate b B ++ ls) f) n,
        add_comm]
      congr 1
      · apply Finset.sum_congr rfl
        intro k hk
        have hk' : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
        have he : n+1-k = (n-k)+1 := by omega
        congr 1
        apply mixedDifference_perm _ f hf
        rw [he, List.replicate_succ]
        simpa only [List.append_assoc, List.cons_append] using
          (List.perm_middle (a := B) (l₁ := List.replicate (n-k) B) (l₂ := ls)).append_left
            (List.replicate k A)
      · apply Finset.sum_congr rfl
        intro k hk
        congr 1
        apply mixedDifference_perm _ f hf
        simpa only [List.replicate_succ, List.cons_append, List.append_assoc] using
          (List.perm_middle (a := A)
            (l₁ := List.replicate k A ++ List.replicate (n-k) B) (l₂ := ls))

theorem mixedTop_tensor_binomial {d : ℕ} {f : LineBundle X → ℤ}
    (hf : LineIsoInvariant f) (hdegree : MixedDegreeLE d f) (A B : LineBundle X) :
    mixedTop f (List.replicate d (A.tensor B)) =
      ∑ k ∈ Finset.range (d+1), (d.choose k : ℤ) *
        mixedTop f (List.replicate k A ++ List.replicate (d-k) B) := by
  have he := congrFun (mixedDifference_replicate_tensor_append hf hdegree A B d [] (by simp))
    (structureLineBundle X)
  simpa only [List.append_nil, Finset.sum_apply, Pi.smul_apply, mixedTop, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply] using he

theorem mixedDifference_replicate_pow_append {d : ℕ} {f : LineBundle X → ℤ}
    (hf : LineIsoInvariant f) (hdegree : MixedDegreeLE d f)
    (L : LineBundle X) (n k : ℕ) (ls : List (LineBundle X)) (hlen : k + ls.length = d) :
    mixedDifference (List.replicate k (L.pow n) ++ ls) f =
      n^k • mixedDifference (List.replicate k L ++ ls) f := by
  induction k generalizing ls with
  | zero => simp
  | succ k ih =>
      rw [List.replicate_succ, List.cons_append,
        mixedDifference_pow_cons_of_degree hf hdegree L n _ (by
          simp only [List.length_append, List.length_replicate]; omega)]
      rw [mixedDifference_perm
        (List.perm_middle (a := L) (l₁ := List.replicate k (L.pow n)) (l₂ := ls)).symm f hf,
        ih (L :: ls) (by simp only [List.length_cons]; omega)]
      rw [mixedDifference_perm
        (List.perm_middle (a := L) (l₁ := List.replicate k L) (l₂ := ls)) f hf,
        smul_smul, pow_succ']
      rfl

theorem mixedTop_two_powers {d : ℕ} {f : LineBundle X → ℤ}
    (hf : LineIsoInvariant f) (hdegree : MixedDegreeLE d f)
    (A B : LineBundle X) (a b k l : ℕ) (hlen : k+l=d) :
    mixedTop f (List.replicate k (A.pow a) ++ List.replicate l (B.pow b)) =
      (a : ℤ)^k * (b : ℤ)^l * mixedTop f (List.replicate k A ++ List.replicate l B) := by
  have he : mixedDifference (List.replicate k (A.pow a) ++ List.replicate l (B.pow b)) f =
      (a^k * b^l) • mixedDifference (List.replicate k A ++ List.replicate l B) f := by
    rw [mixedDifference_replicate_pow_append hf hdegree A a k _ (by simpa using hlen),
      mixedDifference_perm List.perm_append_comm f hf,
      mixedDifference_replicate_pow_append hf hdegree B b l _ (by
        simp only [List.length_replicate]; omega),
      mixedDifference_perm List.perm_append_comm f hf, smul_smul]
  have hev := congrFun he (structureLineBundle X)
  simpa only [Pi.smul_apply, mixedTop, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply,
    Nat.cast_mul, Nat.cast_pow, mul_assoc] using hev

theorem mixedTop_tensor_powers_binomial {d : ℕ} {f : LineBundle X → ℤ}
    (hf : LineIsoInvariant f) (hdegree : MixedDegreeLE d f)
    (A B : LineBundle X) (a b : ℕ) :
    mixedTop f (List.replicate d ((A.pow a).tensor (B.pow b))) =
      ∑ k ∈ Finset.range (d+1), (d.choose k : ℤ) * (a : ℤ)^k * (b : ℤ)^(d-k) *
        mixedTop f (List.replicate k A ++ List.replicate (d-k) B) := by
  rw [mixedTop_tensor_binomial hf hdegree]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ d := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  rw [mixedTop_two_powers hf hdegree A B a b k (d-k) (by omega)]
  ring

theorem mixedDifference_two_powers_append {d : ℕ} {f : LineBundle X → ℤ}
    (hf : LineIsoInvariant f) (hdegree : MixedDegreeLE d f)
    (A B : LineBundle X) (a b k l : ℕ) (ls : List (LineBundle X))
    (hlen : k+l+ls.length=d) :
    mixedDifference (List.replicate k (A.pow a) ++ List.replicate l (B.pow b) ++ ls) f =
      (a^k * b^l) • mixedDifference (List.replicate k A ++ List.replicate l B ++ ls) f := by
  have hswap (as bs : List (LineBundle X)) :
      mixedDifference (as ++ bs ++ ls) f = mixedDifference (bs ++ as ++ ls) f :=
    mixedDifference_perm (List.perm_append_comm.append_right ls) f hf
  rw [List.append_assoc,
    mixedDifference_replicate_pow_append hf hdegree A a k _ (by
      simp only [List.length_append, List.length_replicate]; omega),
    ← List.append_assoc, hswap,
    List.append_assoc,
    mixedDifference_replicate_pow_append hf hdegree B b l _ (by
      simp only [List.length_append, List.length_replicate]; omega),
    ← List.append_assoc, hswap, smul_smul]

theorem mixedTop_tensor_powers_binomial_append {d : ℕ} {f : LineBundle X → ℤ}
    (hf : LineIsoInvariant f) (hdegree : MixedDegreeLE d f)
    (A B : LineBundle X) (a b n : ℕ) (ls : List (LineBundle X))
    (hlen : n+ls.length=d) :
    mixedTop f (List.replicate n ((A.pow a).tensor (B.pow b)) ++ ls) =
      ∑ k ∈ Finset.range (n+1), (n.choose k : ℤ) * (a : ℤ)^k * (b : ℤ)^(n-k) *
        mixedTop f (List.replicate k A ++ List.replicate (n-k) B ++ ls) := by
  have hsum := congrFun
    (mixedDifference_replicate_tensor_append hf hdegree (A.pow a) (B.pow b) n ls hlen)
    (structureLineBundle X)
  change mixedDifference _ f (structureLineBundle X) = _
  rw [hsum]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  rw [mixedDifference_two_powers_append hf hdegree A B a b k (n-k) ls (by omega)]
  simp only [Pi.smul_apply, mixedTop, nsmul_eq_mul, Pi.mul_apply, Nat.cast_mul, Nat.cast_pow,
    Pi.pow_apply, Pi.natCast_apply]
  ring

end
end PiExponent.NumericalAmpleness

end OAI
