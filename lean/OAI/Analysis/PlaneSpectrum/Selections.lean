import OAI.Analysis.PlaneSpectrum.NumberFields

namespace OAI

noncomputable section
open Module
namespace EuclideanFiveColor.GeneralPosition
variable {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]

/-- A cover evaluated at a large general-position set contains a spanning monochromatic subset. -/
lemma spanning_selection {ι : Type*} (Q : Finset ι) (S : Finset V) (hS : General S)
    (hcard : Q.card*(finrank ℚ V-1) < S.card)
    (A : ι → V → Prop) (hA : ∀ x ∈ S, ∃ i ∈ Q, A i x) :
    ∃ i ∈ Q, ∃ T ⊆ S, T.card = finrank ℚ V ∧
      Submodule.span ℚ (T : Set V) = ⊤ ∧ ∀ x ∈ T, A i x := by
  classical
  choose f hfQ hfA using fun x : S => hA x x.property
  have hs : Fintype.card Q * (finrank ℚ V-1) < Fintype.card S := by simpa using hcard
  let g : S → Q := fun x => ⟨f x,hfQ x⟩
  obtain ⟨i,hi⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card g hs
  have hi' : finrank ℚ V ≤ (S.filter (fun x => A i x)).card := by
    have hx : (Finset.univ.filter (fun x : S => g x = i)).card ≤
        (S.filter (fun x => A i x)).card := by
      apply Finset.card_le_card_of_injOn (fun x : S => x.val)
      · intro x hx
        have hg : g x = i := (Finset.mem_filter.mp hx).2
        exact Finset.mem_filter.mpr ⟨x.property,by
          have hh := hfA x
          change A (g x).val x.val at hh
          rwa [hg] at hh⟩
      · intro x hx y hy hxy
        exact Subtype.ext hxy
    omega
  obtain ⟨T,hT,hTc⟩ := Finset.exists_subset_card_eq hi'
  have hTS : T ⊆ S := fun x hx => (Finset.mem_filter.mp (hT hx)).1
  exact ⟨i,i.property,T,hTS,hTc,hS.spans hTS hTc, fun x hx => (Finset.mem_filter.mp (hT hx)).2⟩
end EuclideanFiveColor.GeneralPosition
end

noncomputable section
namespace EuclideanFiveColor.Arithmetic

lemma common_denominator {ι : Type*} [Fintype ι] (c : ι → ℚ) :
    ∃ D : ℕ, 0 < D ∧ ∃ a : ι → ℤ, ∀ i, (D:ℚ)*c i = a i := by
  classical
  let D := ∏ i, (c i).den
  let a := fun i => ((∏ j ∈ Finset.univ.erase i, (c j).den : ℕ) : ℤ)*(c i).num
  refine ⟨D,Finset.prod_pos (fun _ _ => Rat.den_pos _),a,fun i => ?_⟩
  have hD : D = (∏ j ∈ Finset.univ.erase i, (c j).den)*(c i).den :=
    (Finset.prod_erase_mul _ _ (Finset.mem_univ i)).symm
  rw [hD, Nat.cast_mul, mul_assoc, Rat.den_mul_eq_num]
  simp only [a, Int.cast_mul, Int.cast_natCast]

lemma uniform_integral_representations {ι : Type*} [Fintype ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)]
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (v : ∀ i, κ i → V) (x y : V)
    (hx : ∀ i, ∃ c : κ i → ℚ, ∑ j, c j • v i j = x)
    (hy : ∀ i, ∃ c : κ i → ℚ, ∑ j, c j • v i j = y) :
    ∃ D M : ℕ, 0 < D ∧ 0 < M ∧ ∃ a b : ∀ i, κ i → ℤ, ∀ i : ι,
      (∑ j, a i j • v i j) = D • x ∧
      (∑ j, b i j • v i j) = D • y ∧
      (∑ j : κ i, ((a i j).natAbs+(b i j).natAbs)) ≤ M := by
  classical
  choose c hc using hx
  choose d hd using hy
  let f : (Σ i, κ i) × Bool → ℚ := fun p => if p.2 then c p.1.1 p.1.2 else d p.1.1 p.1.2
  obtain ⟨D,hD,A,hA⟩ := common_denominator f
  let a := fun (i : ι) (j : κ i) => A (⟨i,j⟩,true)
  let b := fun (i : ι) (j : κ i) => A (⟨i,j⟩,false)
  let m := fun i => ∑ j : κ i, ((a i j).natAbs+(b i j).natAbs)
  let M := (∑ i, m i)+1
  refine ⟨D,M,hD,Nat.zero_lt_succ _,a,b,fun i => ⟨?_,?_,?_⟩⟩
  · calc
      (∑ j, a i j • v i j) = ∑ j, ((D:ℚ)*c i j) • v i j := by
        apply Finset.sum_congr rfl
        intro j _
        have hh := hA (⟨i,j⟩,true)
        simp only [f,ite_true] at hh
        rw [hh,Int.cast_smul_eq_zsmul]
      _ = (D:ℚ) • ∑ j, c i j • v i j := by simp only [Finset.smul_sum,smul_smul]
      _ = D • x := by rw [hc,Nat.cast_smul_eq_nsmul]
  · calc
      (∑ j, b i j • v i j) = ∑ j, ((D:ℚ)*d i j) • v i j := by
        apply Finset.sum_congr rfl
        intro j _
        have hh := hA (⟨i,j⟩,false)
        simp only [f,Bool.false_eq_true,ite_false] at hh
        rw [hh,Int.cast_smul_eq_zsmul]
      _ = (D:ℚ) • ∑ j, d i j • v i j := by simp only [Finset.smul_sum,smul_smul]
      _ = D • y := by rw [hd,Nat.cast_smul_eq_nsmul]
  · exact (Finset.single_le_sum (fun j _ => Nat.zero_le (m j)) (Finset.mem_univ i)).trans (Nat.le_succ _)
end EuclideanFiveColor.Arithmetic
end

noncomputable section
open Module
namespace EuclideanFiveColor.Arithmetic
open AlgebraicCayley GeneralPosition

lemma span_mult_rep (N : IntermediateField ℚ ℂ) (T : Finset N)
    (hT : Submodule.span ℚ (T : Set N) = ⊤) (q : N) (hq : q ≠ 0) (x : N) :
    ∃ c : T → ℚ, ∑ j, c j • (q*j.val) = x := by
  have hs : Set.range (fun j : T => j.val) = (T : Set N) := Subtype.range_coe
  have hx : q⁻¹*x ∈ Submodule.span ℚ (Set.range (fun j : T => j.val)) := by rw [hs,hT]; trivial
  obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp hx
  refine ⟨c,?_⟩
  calc
    (∑ j, c j • (q*j.val)) = q * ∑ j, c j • j.val := by
      simp only [Finset.mul_sum, mul_smul_comm]
    _ = x := by rw [hc,← mul_assoc,mul_inv_cancel₀ hq,one_mul]

/-- Uniform integral spanning selections extracted from the source's syndetic cover. -/
lemma uniform_selection (Q : Finset ℂ)
    (hQn : ∀ q ∈ Q, ‖q‖ = 1) (hQa : ∀ q ∈ Q, IsAlgebraic ℚ q)
    (A : ℂ → Prop)
    (hA : ∀ v : ℂ, ‖v‖ = 1 → IsAlgebraic ℚ v → ∃ q ∈ Q, A (q*v)) :
    ∃ D M : ℕ, 0 < D ∧ 0 < M ∧ ∀ v : ℂ, ‖v‖ = 1 → IsAlgebraic ℚ v →
      ∃ n : ℕ, ∃ k : Fin n → ℂ, ∃ a b : Fin n → ℤ,
        (∀ j, ‖k j‖ = 1 ∧ IsAlgebraic ℚ (k j) ∧ A (k j*v)) ∧
        (∑ j, a j • k j) = D • (1:ℂ) ∧
        (∑ j, b j • k j) = D • Complex.I ∧
        (∑ j, ((a j).natAbs+(b j).natAbs)) ≤ M := by
  classical
  let N := generatedField Q
  have : FiniteDimensional ℚ N := generatedField_finite Q hQa
  obtain ⟨S,hSc,hSn,hSg⟩ := numberField_general_position N (generatedField_I Q)
    (generatedField_re_closed Q) (generatedField_im_closed Q)
    (Q.card*(finrank ℚ N-1)+1)
  let TS : Finset (Finset N) := S.powerset.filter (fun T => Submodule.span ℚ (T:Set N) = ⊤)
  let I := Q × TS
  let κ : I → Type := fun i => i.2.val
  let qs : Q → N := fun q => ⟨q.val,generatedField_contains Q q.val q.property⟩
  have hqs (q : Q) : qs q ≠ 0 := by
    intro he
    have hec := congrArg (fun z : N => (z:ℂ)) he
    have hn := hQn q q.property
    change q.val = 0 at hec
    simp [hec] at hn
  let k : ∀ i : I, κ i → N := fun i j => qs i.1*j.val
  have hs (i : I) : Submodule.span ℚ (i.2.val:Set N) = ⊤ := (Finset.mem_filter.mp i.2.property).2
  obtain ⟨D,M,hD,hM,a,b,hab⟩ := uniform_integral_representations k (1:N) (iN N (generatedField_I Q))
    (fun i => span_mult_rep N i.2.val (hs i) _ (hqs _) _)
    (fun i => span_mult_rep N i.2.val (hs i) _ (hqs _) _)
  refine ⟨D,M,hD,hM,fun v hv hva => ?_⟩
  have hAlg (z : N) : IsAlgebraic ℚ (z:ℂ) :=
    IsAlgebraic.algHom N.val (IsAlgebraic.of_finite ℚ z)
  obtain ⟨q,hq,T,hTS,hTc,hTspan,hTA⟩ := spanning_selection Q S hSg (by omega)
    (fun q s => A (q*(s:ℂ)*v)) (by
      intro s hs
      have hn : ‖(s:ℂ)*v‖ = 1 := by rw [norm_mul,hSn s hs,hv,one_mul]
      obtain ⟨q,hq,hqA⟩ := hA ((s:ℂ)*v) hn ((hAlg s).mul hva)
      exact ⟨q,hq,by simpa only [mul_assoc] using hqA⟩)
  have hTmem : T ∈ TS := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hTS,hTspan⟩
  let i : I := (⟨q,hq⟩,⟨T,hTmem⟩)
  let e := (Fintype.equivFin (κ i)).symm
  refine ⟨Fintype.card (κ i),fun j => (k i (e j):ℂ),fun j => a i (e j),fun j => b i (e j),?_,?_,?_,?_⟩
  · intro j
    have hj : (e j).val ∈ T := (e j).property
    refine ⟨?_,hAlg (k i (e j)),?_⟩
    · change ‖q*((e j).val:ℂ)‖ = 1
      rw [norm_mul,hQn q hq,hSn _ (hTS hj),one_mul]
    · exact hTA _ hj
  · have he := congrArg (fun z : N => (z:ℂ)) (hab i).1
    push_cast at he
    rw [← he]
    exact Fintype.sum_equiv e _ _ (fun _ => by simp)
  · have he := congrArg (fun z : N => (z:ℂ)) (hab i).2.1
    push_cast at he
    change (∑ j, b i j • (k i j:ℂ)) = D • Complex.I at he
    rw [← he]
    exact Fintype.sum_equiv e _ _ (fun _ => by simp)
  · rw [Fintype.sum_equiv e _ (fun j => (a i j).natAbs+(b i j).natAbs) (fun _ => rfl)]
    exact (hab i).2.2
end EuclideanFiveColor.Arithmetic
end

noncomputable section
namespace EuclideanFiveColor.Arithmetic

lemma real_sum_bound {ι : Type*} [Fintype ι] (a : ι → ℤ) (x : ι → ℝ) (B : ℝ)
    (hx : ∀ i, |x i| ≤ B) :
    |∑ i, (a i : ℝ)*x i| ≤ (∑ i, ((a i).natAbs : ℝ))*B := by
  calc
    _ ≤ ∑ i, |(a i:ℝ)*x i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ((a i).natAbs : ℝ)*B := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      have he : |(a i:ℝ)| = ((a i).natAbs : ℝ) := by simp
      rw [he]
      exact mul_le_mul_of_nonneg_left (hx i) (Nat.cast_nonneg _)
    _ = _ := (Finset.sum_mul _ _ _).symm

lemma selection_transverse {ι : Type*} [Fintype ι] (k : ι → ℂ) (a b : ι → ℤ)
    (D M : ℕ) (hD : 0 < D)
    (ha : (∑ i, a i • k i) = D • (1:ℂ))
    (hb : (∑ i, b i • k i) = D • Complex.I)
    (hM : (∑ i, ((a i).natAbs+(b i).natAbs)) ≤ M)
    (v : ℂ) (hv : ‖v‖ = 1) :
    ∃ i, ∀ j, |(k j*v).re| ≤ |(k i*v).re| ∧
      (D:ℝ) ≤ (M:ℝ)*|(k i*v).re| := by
  classical
  have hn : Nonempty ι := by
    by_contra hh
    have : IsEmpty ι := not_nonempty_iff.mp hh
    have he : (D:ℂ) = 0 := by simpa using ha.symm
    have : D = 0 := by exact_mod_cast he
    omega
  have := hn
  obtain ⟨i,_,him⟩ := Finset.exists_max_image Finset.univ (fun j => |(k j*v).re|) Finset.univ_nonempty
  have hm (j : ι) : |(k j*v).re| ≤ |(k i*v).re| := him j (Finset.mem_univ j)
  have h1 : (∑ j, (a j:ℝ)*(k j*v).re) = (D:ℝ)*v.re := by
    have he := congrArg (fun z : ℂ => (z*v).re) ha
    simpa only [Finset.sum_mul, Complex.re_sum, zsmul_eq_mul, nsmul_eq_mul,
      mul_assoc, Complex.mul_re, Complex.intCast_re, Complex.intCast_im, zero_mul,
      sub_zero, Complex.natCast_re, Complex.natCast_im, Complex.one_re, Complex.one_im,
      mul_one] using he
  have h2 : (∑ j, (b j:ℝ)*(k j*v).re) = -(D:ℝ)*v.im := by
    have he := congrArg (fun z : ℂ => (z*v).re) hb
    simpa only [Finset.sum_mul, Complex.re_sum, zsmul_eq_mul, nsmul_eq_mul,
      mul_assoc, Complex.mul_re, Complex.intCast_re, Complex.intCast_im, zero_mul,
      sub_zero, Complex.natCast_re, Complex.natCast_im, Complex.I_re, Complex.I_im,
      one_mul, zero_sub, mul_neg, neg_mul] using he
  have h1b := real_sum_bound a (fun j => (k j*v).re) _ hm
  have h2b := real_sum_bound b (fun j => (k j*v).re) _ hm
  rw [h1,abs_mul,abs_of_nonneg (Nat.cast_nonneg D)] at h1b
  rw [h2,abs_mul,abs_neg,abs_of_nonneg (Nat.cast_nonneg D)] at h2b
  have hcomp : 1 ≤ |v.re|+|v.im| := hv ▸ Complex.norm_le_abs_re_add_abs_im v
  have hMc : (∑ j, ((a j).natAbs:ℝ))+(∑ j, ((b j).natAbs:ℝ)) ≤ (M:ℝ) := by
    have he : ((∑ j, ((a j).natAbs+(b j).natAbs) : ℕ):ℝ) =
        (∑ j, ((a j).natAbs:ℝ))+(∑ j, ((b j).natAbs:ℝ)) := by
      simp [Finset.sum_add_distrib]
    rw [← he]
    exact_mod_cast hM
  have hexp := mul_le_mul_of_nonneg_right hMc (abs_nonneg (k i*v).re)
  have hfinal : (D:ℝ) ≤ (M:ℝ)*|(k i*v).re| := by
    nlinarith [mul_le_mul_of_nonneg_left hcomp (Nat.cast_nonneg D)]
  exact ⟨i,fun j => ⟨hm j,hfinal⟩⟩
end EuclideanFiveColor.Arithmetic
end

noncomputable section
namespace EuclideanFiveColor.CappedResidues
variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
variable (m : α → ℝ) (hm0 : m 0 = 1)
  (hd : ∀ a b : α, 0 ≤ a → 0 ≤ b → m a * m b ≤ m |a-b|)
  (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)

def Good (n : ℕ) (x : α) : Prop := c^n ≤ m x
include hc0 hc1 in
omit [Field α] [LinearOrder α] [IsStrictOrderedRing α] in
lemma good_mono {n k : ℕ} {x : α} (h : Good m c n x) (hnk : n ≤ k) : Good m c k x :=
  (pow_le_pow_of_le_one hc0 hc1 hnk).trans h
include hm0 hc0 hc1 in
omit [LinearOrder α] [IsStrictOrderedRing α] in
lemma good_zero (n : ℕ) : Good m c n 0 := by
  unfold Good
  rw [hm0]
  exact pow_le_one₀ hc0 hc1
include hd hc0 in
omit [IsStrictOrderedRing α] in
lemma good_diff {n k : ℕ} {a b : α} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : Good m c n a) (hB : Good m c k b) : Good m c (n+k) |a-b| := by
  unfold Good at *
  rw [pow_add]
  exact (mul_le_mul hA hB (pow_nonneg hc0 k) ((pow_nonneg hc0 n).trans hA)).trans (hd a b ha hb)

variable {p : α} (hp : 0 < p) (hpG : Good m c 1 p)
include hd hc0 hc1 hp hpG in
lemma add_residues {a b : α} {n k : ℕ} (ha : a ∈ Set.Ico 0 p) (hb : b ∈ Set.Ico 0 p)
    (hA : Good m c n a) (hB : Good m c k b) :
    ∃ r : α, r ∈ Set.Ico 0 p ∧ Good m c (n+k+2) r ∧ ∃ j : ℤ, a+b = r+j•p := by
  obtain ⟨ha0, hap⟩ := ha
  obtain ⟨hb0, hbp⟩ := hb
  have ha : a ∈ Set.Ico 0 p := ⟨ha0,hap⟩
  have hb : b ∈ Set.Ico 0 p := ⟨hb0,hbp⟩
  by_cases hs : a+b < p
  · refine ⟨a+b, ⟨add_nonneg ha.1 hb.1, hs⟩, ?_, 0, by simp⟩
    have hpa : Good m c (1+n) (p-a) := by
      simpa only [abs_of_nonneg (sub_nonneg.mpr ha.2.le)] using
        good_diff m hd c hc0 hp.le ha.1 hpG hA
    have hsub : Good m c (1+n+k) ((p-a)-b) := by
      simpa only [abs_of_nonneg (show 0 ≤ (p-a)-b by linarith)] using
        good_diff m hd c hc0 (sub_nonneg.mpr ha.2.le) hb.1 hpa hB
    have hfinal := good_diff m hd c hc0 hp.le (show 0 ≤ (p-a)-b by linarith) hpG hsub
    have he : |p-((p-a)-b)| = a+b := by rw [abs_of_nonneg (by linarith)]; abel
    simpa only [he, show 1+(1+n+k) = n+k+2 by omega] using hfinal
  · refine ⟨a+b-p, ⟨by linarith, by linarith⟩, ?_, 1, by simp⟩
    have hpb : Good m c (1+k) (p-b) := by
      simpa only [abs_of_nonneg (sub_nonneg.mpr hb.2.le)] using
        good_diff m hd c hc0 hp.le hb.1 hpG hB
    have hfinal := good_diff m hd c hc0 ha.1 (sub_nonneg.mpr hb.2.le) hA hpb
    have he : |a-(p-b)| = a+b-p := by rw [abs_of_nonneg (by linarith)]; abel
    apply good_mono m c hc0 hc1 (n := n+(1+k)) (hnk := by omega)
    simpa only [he] using hfinal

include hm0 hd hc0 hc1 hp hpG in
lemma input_residue {x : α} (hx : |x| ≤ p) (hG : Good m c 1 |x|) :
    ∃ r : α, r ∈ Set.Ico 0 p ∧ Good m c 2 r ∧ ∃ j : ℤ, x = r+j•p := by
  by_cases hx0 : 0 ≤ x
  · have hxp : x ≤ p := by simpa [abs_of_nonneg hx0] using hx
    rcases lt_or_eq_of_le hxp with hlt | rfl
    · exact ⟨x, ⟨hx0,hlt⟩, good_mono m c hc0 hc1 (by simpa [abs_of_nonneg hx0] using hG) (by omega), 0, by simp⟩
    · exact ⟨0, ⟨le_rfl,hp⟩, good_zero m hm0 c hc0 hc1 2, 1, by simp⟩
  · have hn : 0 < -x := neg_pos.mpr (lt_of_not_ge hx0)
    have hnx : -x ≤ p := by simpa [abs_of_neg (lt_of_not_ge hx0)] using hx
    rcases lt_or_eq_of_le hnx with hlt | heq
    · refine ⟨p+x, ⟨by linarith, by linarith⟩, ?_, -1, by simp⟩
      have hneg : Good m c 1 (-x) := by simpa [abs_of_neg (lt_of_not_ge hx0)] using hG
      have hfinal := good_diff m hd c hc0 hp.le hn.le hpG hneg
      simpa only [show |p- -x| = p+x by rw [sub_neg_eq_add, abs_of_nonneg (by linarith)]] using hfinal
    · refine ⟨0, ⟨le_rfl,hp⟩, good_zero m hm0 c hc0 hc1 2, -1, ?_⟩
      simp only [neg_smul, one_smul, zero_add]
      linarith

include hm0 hd hc0 hc1 hp hpG in
lemma list_residue (l : List α) (hl : ∀ x∈l, |x| ≤ p ∧ Good m c 1 |x|) :
    ∃ r : α, r ∈ Set.Ico 0 p ∧ Good m c (4*l.length) r ∧ ∃ j : ℤ, l.sum = r+j•p := by
  induction l with
  | nil => exact ⟨0, ⟨le_rfl,hp⟩, good_zero m hm0 c hc0 hc1 _, 0, by simp⟩
  | cons x l ih =>
    obtain ⟨a,ha,hA,i,hi⟩ := input_residue m hm0 hd c hc0 hc1 hp hpG (hl x (List.mem_cons_self)).1 (hl x (List.mem_cons_self)).2
    obtain ⟨b,hb,hB,j,hj⟩ := ih (fun y hy => hl y (List.mem_cons_of_mem x hy))
    obtain ⟨r,hr,hR,k,hk⟩ := add_residues m hd c hc0 hc1 hp hpG ha hb hA hB
    refine ⟨r,hr,?_,i+j+k,?_⟩
    · simpa only [List.length_cons, show 2+4*l.length+2 = 4*(l.length+1) by omega] using hR
    · simp only [List.sum_cons, hi, hj, add_zsmul]
      calc
        _ = (a+b)+(i•p+j•p) := by abel
        _ = _ := by rw [hk]; abel

include hm0 hd hc0 hc1 hp hpG in
lemma list_cap (l : List α) (hl : ∀ x∈l, |x| ≤ p ∧ Good m c 1 |x|)
    (hz : l.sum ∈ Set.Ico 0 p) : Good m c (4*l.length) l.sum := by
  obtain ⟨r,hr,hR,j,hj⟩ := list_residue m hm0 hd c hc0 hc1 hp hpG l hl
  have hzero : j = 0 := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with hn | hn
    · have hle : j ≤ -1 := by omega
      have hh : j•p ≤ (-1:ℤ)•p := by
        simp only [zsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hle) hp.le
      simp only [neg_smul, one_smul] at hh
      linarith [hz.1, hr.2]
    · have hge : 1 ≤ j := by omega
      have hh : (1:ℤ)•p ≤ j•p := by
        simp only [zsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hge) hp.le
      simp only [one_smul] at hh
      linarith [hz.2, hr.1]
  have he : l.sum = r := by simpa only [hzero, zero_smul, add_zero] using hj
  rw [he]
  exact hR
end EuclideanFiveColor.CappedResidues
end

noncomputable section
namespace EuclideanFiveColor.CappedResidues
variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

def signedList (a : ℤ) (x : α) : List α :=
  match a with
  | .ofNat n => List.replicate n x
  | .negSucc n => List.replicate (n+1) (-x)
omit [LinearOrder α] [IsStrictOrderedRing α] in
@[simp] lemma signedList_length (a : ℤ) (x : α) : (signedList a x).length = a.natAbs := by
  cases a <;> simp [signedList]
omit [LinearOrder α] [IsStrictOrderedRing α] in
@[simp] lemma signedList_sum (a : ℤ) (x : α) : (signedList a x).sum = a • x := by
  cases a <;> simp [signedList]
  ring
omit [IsStrictOrderedRing α] in
lemma signedList_mem (a : ℤ) (x v : α) (hv : v ∈ signedList a x) : |v| = |x| := by
  cases a <;> simp only [signedList,List.mem_replicate] at hv
  · rw [hv.2]
  · rw [hv.2,abs_neg]

omit [IsStrictOrderedRing α] in
lemma integer_list {ι : Type*} (s : Finset ι) (a : ι → ℤ) (x : ι → α) :
    ∃ l : List α, l.length = ∑ i ∈ s, (a i).natAbs ∧ l.sum = ∑ i ∈ s, a i • x i ∧
      ∀ v ∈ l, ∃ i ∈ s, |v| = |x i| := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨[],by simp,by simp,by simp⟩
  | @insert i s hi ih =>
    obtain ⟨l,hl,hs,hv⟩ := ih
    refine ⟨signedList (a i) (x i) ++ l,?_,?_,?_⟩
    · simp [hl,hi]
    · simp [hs,hi]
    · intro v hv'
      rcases List.mem_append.mp hv' with hv' | hv'
      · exact ⟨i,Finset.mem_insert_self _ _,signedList_mem _ _ _ hv'⟩
      · obtain ⟨j,hj,he⟩ := hv v hv'
        exact ⟨j,Finset.mem_insert_of_mem hj,he⟩

variable (m : α → ℝ) (hm0 : m 0 = 1)
  (hd : ∀ a b : α, 0 ≤ a → 0 ≤ b → m a*m b ≤ m |a-b|)
  (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
  {p : α} (hp : 0 < p) (hpG : Good m c 1 p)
include hm0 hd hc0 hc1 hp hpG in
lemma integer_cap {ι : Type*} (s : Finset ι) (a : ι → ℤ) (x : ι → α)
    (hx : ∀ i ∈ s, |x i| ≤ p ∧ Good m c 1 |x i|)
    (hz : (∑ i ∈ s, a i • x i) ∈ Set.Ico 0 p) :
    Good m c (4*∑ i ∈ s, (a i).natAbs) (∑ i ∈ s, a i • x i) := by
  obtain ⟨l,hl,hs,hv⟩ := integer_list s a x
  have he := list_cap m hm0 hd c hc0 hc1 hp hpG l (by
    intro v hvl
    obtain ⟨i,hi,he⟩ := hv v hvl
    rw [he]
    exact hx i hi) (hs.symm ▸ hz)
  rwa [hl,hs] at he
include hm0 hd hc0 hc1 hp hpG in
lemma integer_abs_cap {ι : Type*} (s : Finset ι) (a : ι → ℤ) (x : ι → α)
    (hx : ∀ i ∈ s, |x i| ≤ p ∧ Good m c 1 |x i|)
    (hz : |∑ i ∈ s, a i • x i| < p) :
    Good m c (4*∑ i ∈ s, (a i).natAbs) |∑ i ∈ s, a i • x i| := by
  by_cases hn : 0 ≤ ∑ i ∈ s, a i • x i
  · rw [abs_of_nonneg hn] at hz ⊢
    exact integer_cap m hm0 hd c hc0 hc1 hp hpG s a x hx ⟨hn,hz⟩
  · have hs : (∑ i ∈ s, a i • (-x i)) = -∑ i ∈ s, a i • x i := by simp
    have hz' : (∑ i ∈ s, a i • (-x i)) ∈ Set.Ico 0 p := by
      rw [hs]
      have he : |∑ i ∈ s, a i • x i| = -∑ i ∈ s, a i • x i := abs_of_neg (lt_of_not_ge hn)
      exact ⟨by linarith,he ▸ hz⟩
    have he := integer_cap m hm0 hd c hc0 hc1 hp hpG s a (fun i => -x i)
      (fun i hi => by simpa only [abs_neg] using hx i hi) hz'
    simpa only [hs,abs_of_neg (lt_of_not_ge hn)] using he
end EuclideanFiveColor.CappedResidues
end

end OAI
