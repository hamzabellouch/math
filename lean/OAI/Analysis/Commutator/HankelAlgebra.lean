import Mathlib
import OAI.Analysis.Commutator.CornerAlgebra
import OAI.Analysis.Commutator.FreeMoments

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison.FreeMoments

variable {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]

variable {ι : Type*} (S : ι → StarSubalgebra ℂ A) (τ : A →ₗ[ℂ] ℂ)

variable (h1 : τ 1=1) (htr : ∀ a b : A, τ (a*b)=τ (b*a))

include h1 htr in
theorem free_of_different_endpoints
    (hcyc : ∀ (a b : Letter S τ) (m : List (Letter S τ)),
      Reduced (a :: m ++ [b]) → a.color≠b.color → τ (word (a :: m ++ [b]))=0) :
    Free S τ := by
  intro w
  induction hn : w.length using Nat.strong_induction_on generalizing w with
  | h n ih =>
    intro hw hne
    cases w with
    | nil => exact (hne rfl).elim
    | cons a w =>
      cases w using List.reverseRecOn with
      | nil => simpa using a.centered
      | append_singleton m b =>
        by_cases hab : a.color=b.color
        · have hmne : m≠[] := by
            intro hm
            subst m
            exact hw.rel hab
          have hm : Reduced m := hw.tail.left_of_append
          have ham : Reduced (a::m) :=
            (show Reduced ((a::m)++[b]) from hw).left_of_append
          let c : Letter S τ := {
            color := a.color
            val := b.val*a.val - τ (b.val*a.val) • 1
            mem := sub_mem (mul_mem (by simpa [hab] using b.mem) a.mem)
              (SMulMemClass.smul_mem _ (one_mem _))
            centered := by simp [map_sub, map_smul, h1] }
          have hc : Reduced (c::m) := by
            apply ham.imp_head
            intro z hz
            exact hz
          have hc0 : τ (word (c::m)) = 0 :=
            ih _ (by simp at hn ⊢; omega) (c::m) rfl hc (by simp)
          have hm0 : τ (word m)=0 := ih _ (by simp at hn ⊢; omega) m rfl hm hmne
          have heq : word (c::m) = b.val*a.val*word m - τ (b.val*a.val) • word m := by
            simp [word_cons, c, sub_mul]
          rw [heq, map_sub, map_smul, hm0, smul_zero, sub_zero] at hc0
          rw [word_cons, word_append, word_cons, word_nil, mul_one]
          calc
            τ (a.val * (word m*b.val)) = τ (b.val*(a.val*word m)) := by
              rw [←mul_assoc, htr]
            _ = 0 := by simpa only [mul_assoc] using hc0
        · exact hcyc a b m hw hab

end Kadison.FreeMoments

namespace Kadison.FreeMoments

variable {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]

variable {ι : Type*}

omit [StarRing A] [StarModule ℂ A] in
lemma product_vanish_on_spans (B : ι → Set A) (colors : List ι) (φ : A →ₗ[ℂ] ℂ)
    (h : ∀ v : List A, List.Forall₂ (fun i x => x ∈ B i) colors v → φ v.prod=0) :
    ∀ v : List A, List.Forall₂ (fun i x => x ∈ Submodule.span ℂ (B i)) colors v → φ v.prod=0 := by
  induction colors generalizing φ with
  | nil => intro v hv; cases hv; exact h [] .nil
  | cons i colors ih =>
    intro v hv
    cases hv with
    | cons hx hv =>
      rename_i x v
      let ψ : A →ₗ[ℂ] ℂ := φ.comp (LinearMap.mulLeft ℂ x)
      apply ih ψ ?_ v hv
      intro w hw
      change φ (x*w.prod)=0
      induction hx using Submodule.span_induction with
      | mem x hx => exact h (x::w) (.cons hx hw)
      | zero => simp
      | add x y _ _ hx hy => simp only [add_mul, map_add, hx, hy, add_zero]
      | smul c x _ hx => simp only [smul_mul_assoc, map_smul, hx, smul_zero]

variable (S : ι → StarSubalgebra ℂ A) (τ : A →ₗ[ℂ] ℂ)

lemma letterList_of_values {colors : List ι} {v : List A}
    (hv : List.Forall₂ (fun i x => x∈S i ∧ τ x=0) colors v) :
    ∃ w : List (Letter S τ), w.map Letter.color=colors ∧ w.map Letter.val=v := by
  induction hv with
  | nil => exact ⟨[],rfl,rfl⟩
  | @cons i x colors v hx hv ih =>
    obtain ⟨w,hwc,hwv⟩ := ih
    exact ⟨⟨i,x,hx.1,hx.2⟩::w, by simp [hwc], by simp [hwv]⟩

theorem free_of_spanning_alphabets (B : ι → Set A)
    (hspan : ∀ i x, x∈S i → τ x=0 → x∈Submodule.span ℂ (B i))
    (hvan : ∀ (colors : List ι) (v : List A),
      colors.IsChain (·≠·) → colors≠[] →
      List.Forall₂ (fun i x => x∈B i) colors v → τ v.prod=0) : Free S τ := by
  intro w hw hne
  let colors := w.map Letter.color
  have hchain : colors.IsChain (·≠·) := (List.isChain_map _).mpr hw
  have hcne : colors≠[] := by simpa [colors] using hne
  apply product_vanish_on_spans B colors τ (hvan colors · hchain hcne) (w.map Letter.val)
  change List.Forall₂ (fun i x => x∈Submodule.span ℂ (B i)) (w.map Letter.color) (w.map Letter.val)
  clear hw hne hchain hcne colors
  induction w with
  | nil => exact .nil
  | cons a w ih => exact .cons (hspan a.color a.val a.mem a.centered) ih

end Kadison.FreeMoments

namespace Kadison.FreeMoments

variable {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]

variable {ι : Type*} {S : ι → StarSubalgebra ℂ A} {τ : A →ₗ[ℂ] ℂ}

def paired (s : Letter S τ) (v : List (Letter S τ)) : List (Letter S τ) :=
  v.flatMap (fun a => [a,s])

@[simp] lemma paired_nil (s : Letter S τ) : paired s []=[] := rfl

@[simp] lemma paired_cons (s a : Letter S τ) (v : List (Letter S τ)) :
    paired s (a::v)=a::s::paired s v := rfl

@[simp] lemma paired_append (s : Letter S τ) (v z : List (Letter S τ)) :
    paired s (v++z)=paired s v++paired s z := by simp [paired]

lemma paired_reduced (s : Letter S τ) (v : List (Letter S τ))
    (h : ∀ a∈v, a.color≠s.color) : Reduced (s::paired s v) := by
  induction v with
  | nil => exact List.IsChain.singleton _
  | cons a v ih =>
    apply List.isChain_cons_cons.mpr
    refine ⟨(h a (by simp)).symm, ?_⟩
    apply List.isChain_cons_cons.mpr
    exact ⟨h a (by simp), ih (fun b hb => h b (by simp [hb]))⟩

lemma paired_moment (hfree : Free S τ) (s : Letter S τ) (v : List (Letter S τ))
    (hne : v≠[]) (h : ∀ a∈v, a.color≠s.color) : τ (word (paired s v))=0 := by
  apply hfree _ (paired_reduced s v h).tail
  cases v with
  | nil => exact (hne rfl).elim
  | cons a v => simp

@[simp] lemma word_paired_replicate (s d : Letter S τ) (n : ℕ) :
    word (paired s (List.replicate n d))=(d.val*s.val)^n := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, ih, pow_succ', mul_assoc]

def dihedralBlocks (d : Letter S τ) (v : List (Letter S τ × ℕ)) : List (Letter S τ) :=
  v.flatMap (fun x => x.1 :: List.replicate x.2 d)

lemma word_dihedralBlocks (s d : Letter S τ) (v : List (Letter S τ × ℕ)) :
    word (paired s (dihedralBlocks d v)) =
      (v.map (fun x => x.1.val*s.val*(d.val*s.val)^x.2)).prod := by
  induction v with
  | nil => simp [dihedralBlocks]
  | cons x v ih =>
    simp only [dihedralBlocks, List.flatMap_cons, List.cons_append, paired_cons,
      paired_append, word_cons, word_append, word_paired_replicate,
      List.map_cons, List.prod_cons] at *
    rw [ih]
    simp only [mul_assoc]

theorem dihedral_cyclic_moment (hfree : Free S τ) (s d : Letter S τ)
    (hsd : d.color≠s.color) (v : List (Letter S τ × ℕ)) (hne : v≠[])
    (hcolor : ∀ x∈v, x.1.color≠s.color)
    (hd : ∀ x∈v, x.1.val*d.val=x.1.val) :
    τ ((v.map (fun x => x.1.val*(d.val*s.val)^(x.2+1))).prod)=0 := by
  have hblocks : ∀ a∈dihedralBlocks d v, a.color≠s.color := by
    intro a ha
    obtain ⟨x,hx,ha⟩ := List.mem_flatMap.mp ha
    simp only [List.mem_cons, List.mem_replicate] at ha
    rcases ha with rfl | ⟨_,rfl⟩
    · exact hcolor x hx
    · exact hsd
  have hbne : dihedralBlocks d v≠[] := by
    cases v with
    | nil => exact (hne rfl).elim
    | cons x v => simp [dihedralBlocks]
  have hm := paired_moment hfree s (dihedralBlocks d v) hbne hblocks
  rw [word_dihedralBlocks] at hm
  convert hm using 2
  apply congrArg List.prod
  apply List.map_congr_left
  intro x hx
  rw [pow_succ', ←mul_assoc, ←mul_assoc, hd x hx]

end Kadison.FreeMoments

namespace Kadison.CornerMoments

variable {A : Type*} [Ring A] [Algebra ℂ A]

variable (p : A)

omit [Algebra ℂ A] in
lemma left_support_prod (v : List (A×A)) (hne : v≠[])
    (h : ∀ x∈v, p*x.1=x.1) :
    p * (v.map (fun x => x.1*x.2)).prod = (v.map (fun x => x.1*x.2)).prod := by
  cases v with
  | nil => exact (hne rfl).elim
  | cons x v => simp only [List.map_cons, List.prod_cons, ←mul_assoc, h x (by simp)]

omit [Algebra ℂ A] in
lemma compressed_prod (v : List (A×A)) (hne : v≠[])
    (h : ∀ x∈v, p*x.1=x.1) :
    (v.map (fun x => x.1*x.2*p)).prod = (v.map (fun x => x.1*x.2)).prod*p := by
  induction v with
  | nil => exact (hne rfl).elim
  | cons x v ih =>
    by_cases hv : v=[]
    · subst v; simp
    · have ht : ∀ y∈v, p*y.1=y.1 := fun y hy => h y (by simp [hy])
      simp only [List.map_cons, List.prod_cons]
      rw [ih hv ht]
      simp only [mul_assoc]
      rw [←mul_assoc p, left_support_prod p v hv ht]

lemma traceremove (τ : A →ₗ[ℂ] ℂ) (htr : ∀ a b : A, τ (a*b)=τ (b*a))
    (v : List (A×A)) (hne : v≠[]) (h : ∀ x∈v, p*x.1=x.1) :
    τ ((v.map (fun x => x.1*x.2*p)).prod)=τ ((v.map (fun x => x.1*x.2)).prod) := by
  rw [compressed_prod p v hne h, htr, left_support_prod p v hne h]

end Kadison.CornerMoments

namespace Kadison.DihedralCorner

open scoped ComplexOrder

variable {A : Type*} [CStarAlgebra A]

variable (u d : unitary A)

def wave (n : ℤ) : A := (u^n : unitary A)

@[simp] lemma wave_zero : wave u 0=(1 : A) := by simp [wave]

lemma wave_add (n m : ℤ) : wave u (n+m)=wave u n*wave u m := by
  simp [wave, zpow_add]

@[simp] lemma wave_star (n : ℤ) : star (wave u n)=wave u (-n) := by
  rw [wave, wave, zpow_neg, ←Unitary.star_eq_inv, Unitary.coe_star]

variable (hr : MulAut.conj d u=u⁻¹)

include hr in
lemma reflection_wave (n : ℤ) : (d : A)*wave u n=wave u (-n)*(d : A) := by
  have h : d*u^n=u^(-n)*d := by
    calc
      d*u^n = (MulAut.conj d (u^n))*d := by simp [MulAut.conj_apply, mul_assoc]
      _ = (u⁻¹)^n*d := by rw [map_zpow, hr]
      _ = u^(-n)*d := by simp
  exact congrArg (fun z : unitary A => (z : A)) h

variable {p : A} (hp : IsStarProjection p)
  (hpform : p=(1/2 : ℂ) • (1+(d : A)))

def cosine (n : ℤ) : Corner hp :=
  ⟨p*wave u n*p, by constructor <;> simp [mul_assoc, ←mul_assoc p p, hp.isIdempotentElem.eq]⟩

@[simp] lemma cosine_coe (n : ℤ) : ((cosine u hp n : Corner hp) : A)=p*wave u n*p := rfl

@[simp] lemma cosine_zero : cosine u hp 0=1 := by
  apply Subtype.ext
  simp [hp.isIdempotentElem.eq]

@[simp] lemma cosine_star (n : ℤ) : star (cosine u hp n)=cosine u hp (-n) := by
  apply Subtype.ext
  change star (p*wave u n*p)=p*wave u (-n)*p
  simp only [star_mul, hp.isSelfAdjoint.star_eq, wave_star, mul_assoc]

variable (hpd : p*(d : A)=p) (hdp : (d : A)*p=p)

include hr hpd hdp in
lemma cosine_neg (n : ℤ) : cosine u hp (-n)=cosine u hp n := by
  apply Subtype.ext
  change p*wave u (-n)*p=p*wave u n*p
  calc
    p*wave u (-n)*p = p*wave u (-n)*((d : A)*p) := by rw [hdp]
    _ = p*((d : A)*wave u n)*p := by rw [reflection_wave u d hr n]; noncomm_ring
    _ = p*wave u n*p := by rw [←mul_assoc p, hpd]

include hr hpform hdp in
lemma cosine_mul (n m : ℤ) : cosine u hp n*cosine u hp m =
    (1/2 : ℂ) • (cosine u hp (n+m)+cosine u hp (n-m)) := by
  apply Subtype.ext
  change (p*wave u n*p)*(p*wave u m*p)=
    (1/2 : ℂ) •(p*wave u (n+m)*p+p*wave u (n-m)*p)
  calc
    _ = p*wave u n*(p*p)*wave u m*p := by noncomm_ring
    _ = p*wave u n*p*wave u m*p := by rw [hp.isIdempotentElem.eq]
    _ = (1/2 : ℂ) •(p*wave u n*wave u m*p+p*wave u n*(d : A)*wave u m*p) := by
      conv_lhs => arg 1; arg 1; arg 2; rw [hpform]
      simp only [mul_smul_comm, smul_mul_assoc, mul_add, add_mul, mul_one, mul_assoc]
    _ = (1/2 : ℂ) •(p*wave u (n+m)*p+p*wave u (n-m)*p) := by
      rw [wave_add, sub_eq_add_neg, wave_add]
      apply congrArg ((1/2 : ℂ) • ·)
      apply congrArg₂ (·+·)
      · noncomm_ring
      · calc
          p*wave u n*(d : A)*wave u m*p = p*wave u n*((d : A)*wave u m)*p := by noncomm_ring
          _ = p*wave u n*(wave u (-m)*(d : A))*p := by rw [reflection_wave u d hr m]
          _ = p*(wave u n*wave u (-m))*p := by
            simp only [mul_assoc, hdp]

end Kadison.DihedralCorner

namespace Kadison.DihedralCorner

open scoped ComplexOrder

variable {A : Type*} [CStarAlgebra A]

variable (u d : unitary A) (hr : MulAut.conj d u=u⁻¹)

variable {p : A} (hp : IsStarProjection p) (hpform : p=(1/2 : ℂ) • (1+(d : A)))
  (hpd : p*(d : A)=p) (hdp : (d : A)*p=p)

def cosineSpace : Submodule ℂ (Corner hp) := Submodule.span ℂ (Set.range (cosine u hp))

lemma cosine_mem (n : ℤ) : cosine u hp n∈cosineSpace u hp :=
  Submodule.subset_span ⟨n,rfl⟩

include hr hpform hdp in
lemma cosineSpace_mul {a b : Corner hp} (ha : a∈cosineSpace u hp) (hb : b∈cosineSpace u hp) :
    a*b∈cosineSpace u hp := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨n,rfl⟩ := ha
    induction hb using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨m,rfl⟩ := hb
      rw [cosine_mul u d hr hp hpform hdp]
      exact (cosineSpace u hp).smul_mem _ ((cosineSpace u hp).add_mem
        (cosine_mem u hp _) (cosine_mem u hp _))
    | zero => simp
    | add b c _ _ hb hc => simpa only [mul_add] using (cosineSpace u hp).add_mem hb hc
    | smul z b _ hb => simpa only [mul_smul_comm] using (cosineSpace u hp).smul_mem z hb
  | zero => simp
  | add a c _ _ ha hc => simpa only [add_mul] using (cosineSpace u hp).add_mem ha hc
  | smul z a _ ha => simpa only [smul_mul_assoc] using (cosineSpace u hp).smul_mem z ha

lemma cosineSpace_star {a : Corner hp} (ha : a∈cosineSpace u hp) : star a∈cosineSpace u hp := by
  induction ha using Submodule.span_induction with
  | mem a ha => obtain ⟨n,rfl⟩ := ha; simpa using cosine_mem u hp (-n)
  | zero => simp
  | add a b _ _ ha hb => simpa only [star_add] using (cosineSpace u hp).add_mem ha hb
  | smul z a _ ha => simpa only [star_smul] using (cosineSpace u hp).smul_mem (star z) ha

def cosineAlgebra : StarSubalgebra ℂ (Corner hp) where
  __ : Subalgebra ℂ (Corner hp) :=
    { __ := cosineSpace u hp
      one_mem' := by simpa using cosine_mem u hp 0
      mul_mem' := cosineSpace_mul u d hr hp hpform hdp
      algebraMap_mem' := fun z => by
        change algebraMap ℂ (Corner hp) z∈cosineSpace u hp
        simpa only [Algebra.algebraMap_eq_smul_one] using
          (cosineSpace u hp).smul_mem z (by simpa using cosine_mem u hp 0) }
  star_mem' := cosineSpace_star u hp

def positiveCosines : Set (Corner hp) := Set.range (fun n : ℕ => cosine u hp (n+1))

include hr hpd hdp in
lemma cosine_nonzero_mem_positive {n : ℤ} (hn : n≠0) :
    cosine u hp n∈Submodule.span ℂ (positiveCosines u hp) := by
  by_cases hpos : 0<n
  · obtain ⟨m,hm⟩ := Int.eq_ofNat_of_zero_le hpos.le
    have hm0 : 0 < m := by omega
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm0)
    subst n
    exact Submodule.subset_span ⟨k,by simp⟩
  · have hpos : 0< -n := by omega
    obtain ⟨m,hm⟩ := Int.eq_ofNat_of_zero_le hpos.le
    have hm0 : 0 < m := by omega
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm0)
    have heq : cosine u hp n=cosine u hp (k+1) := by
      rw [←cosine_neg u d hr hp hpd hdp n, hm]
      simp
    rw [heq]
    exact Submodule.subset_span ⟨k,rfl⟩

include hr hpd hdp in
lemma center_cosineSpace (τ : Corner hp →ₗ[ℂ] ℂ) (hτ1 : τ 1=1)
    (hτ0 : ∀ n : ℤ, n≠0 → τ (cosine u hp n)=0)
    {a : Corner hp} (ha : a∈cosineSpace u hp) :
    a-τ a • 1∈Submodule.span ℂ (positiveCosines u hp) := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨n,rfl⟩ := ha
    by_cases hn : n=0
    · subst n; simp [hτ1]
    · rw [hτ0 n hn, zero_smul, sub_zero]
      exact cosine_nonzero_mem_positive u d hr hp hpd hdp hn
  | zero => simp
  | add a b _ _ ha hb =>
    simpa only [map_add, add_smul, add_sub_add_comm] using
      (Submodule.span ℂ (positiveCosines u hp)).add_mem ha hb
  | smul z a _ ha =>
    simpa only [map_smul, smul_eq_mul, mul_smul, smul_sub] using
      (Submodule.span ℂ (positiveCosines u hp)).smul_mem z ha

include hr hpform hpd hdp in
lemma centered_cosineAlgebra_span (τ : Corner hp →ₗ[ℂ] ℂ) (hτ1 : τ 1=1)
    (hτ0 : ∀ n : ℤ, n≠0 → τ (cosine u hp n)=0)
    {a : Corner hp} (ha : a∈cosineAlgebra u d hr hp hpform hdp) (ha0 : τ a=0) :
    a∈Submodule.span ℂ (positiveCosines u hp) := by
  simpa only [ha0, zero_smul, sub_zero] using
    center_cosineSpace u d hr hp hpd hdp τ hτ1 hτ0 ha

end Kadison.DihedralCorner

namespace Kadison.FreeMoments

variable {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]

variable {ι : Type*} {S : ι → StarSubalgebra ℂ A} {τ : A →ₗ[ℂ] ℂ}

lemma alternating_power_centered (hfree : Free S τ) (d s : Letter S τ)
    (hds : d.color≠s.color) (n : ℕ) : τ ((d.val*s.val)^(n+1))=0 := by
  have h := paired_moment hfree s (List.replicate (n+1) d) (by simp)
    (by intro a ha; simpa only [List.mem_replicate] using (show a.color≠s.color from by
      obtain ⟨_,rfl⟩ := List.mem_replicate.mp ha; exact hds))
  rwa [word_paired_replicate] at h

lemma alternating_odd_centered (hfree : Free S τ) (d s : Letter S τ)
    (hds : d.color≠s.color) (n : ℕ) : τ (s.val*(d.val*s.val)^n)=0 := by
  have h := hfree (s::paired s (List.replicate n d))
    (paired_reduced s (List.replicate n d) (by
      intro a ha; obtain ⟨_,rfl⟩ := List.mem_replicate.mp ha; exact hds)) (by simp)
  rwa [word_cons, word_paired_replicate] at h

end Kadison.FreeMoments

namespace Kadison.DihedralCorner

open FreeMoments

variable {A : Type*} [CStarAlgebra A]

variable {ι : Type*} {S : ι → StarSubalgebra ℂ A} (τ : A →ₗ[ℂ] ℂ)

variable (htr : ∀ a b : A, τ (a*b)=τ (b*a)) (hfree : Free S τ)

variable (d s : unitary A) (i j : ι) (hij : i≠j)

variable (hd : (d : A)∈S i) (hs : (s : A)∈S j)
  (hd0 : τ (d : A)=0) (hs0 : τ (s : A)=0)

variable {p : A} (hp : IsStarProjection p) (hpform : p=(1/2 : ℂ) • (1+(d : A)))
  (hd2 : (d : A)*(d : A)=1)

include htr hfree hij hd hs hd0 hs0 hpform hd2 in
lemma cosine_positive_centered (n : ℕ) : τ ((cosine (d*s) hp (n+1) : Corner hp) : A)=0 := by
  let D : Letter S τ := ⟨i,d,hd,hd0⟩
  let F : Letter S τ := ⟨j,s,hs,hs0⟩
  have hpow := alternating_power_centered hfree D F hij n
  have hodd := alternating_odd_centered hfree D F hij n
  change τ (((d : A)*(s : A))^(n+1))=0 at hpow
  change τ ((s : A)*((d : A)*(s : A))^n)=0 at hodd
  have hwave : wave (d*s) (n+1)=((d : A)*(s : A))^(n+1) := by
    change (((d*s)^((n+1 : ℕ) : ℤ) : unitary A) : A)=_
    rw [zpow_natCast]
    simp only [SubmonoidClass.coe_pow, Submonoid.coe_mul]
  have hdw : (d : A)*wave (d*s) (n+1)=(s : A)*((d : A)*(s : A))^n := by
    rw [hwave, pow_succ', ←mul_assoc, ←mul_assoc, hd2, one_mul]
  change τ (p*wave (d*s) (n+1)*p)=0
  rw [htr, ←mul_assoc, hp.isIdempotentElem.eq, hpform]
  rw [smul_mul_assoc, add_mul, one_mul, map_smul, map_add, hwave, hpow]
  rw [←hwave, hdw, hodd]
  simp

end Kadison.DihedralCorner

namespace Kadison

variable {A : Type*} [CStarAlgebra A] {p : A} (hp : IsStarProjection p)

def cornerFactor (D : StarSubalgebra ℂ A) (hpD : p∈D) : StarSubalgebra ℂ (Corner hp) where
  carrier := {a | (a : A)∈D}
  zero_mem' := zero_mem D
  add_mem' := by
    intro a b ha hb
    change (a : A)+(b : A)∈D
    exact add_mem ha hb
  mul_mem' := by
    intro a b ha hb
    change (a : A)*(b : A)∈D
    exact mul_mem ha hb
  one_mem' := hpD
  algebraMap_mem' c := by
    change c • p∈D
    exact D.smul_mem hpD c
  star_mem' := by
    intro a ha
    change star (a : A)∈D
    exact star_mem ha

lemma corner_list_prod_coe (v : List (Corner hp)) (hne : v≠[]) :
    ((v.prod : Corner hp) : A)=(v.map (fun a : Corner hp => (a : A))).prod := by
  induction v with
  | nil => exact (hne rfl).elim
  | cons a v ih =>
    by_cases hv : v=[]
    · subst v; simp
    · simp only [List.prod_cons,List.map_cons,corner_mul]
      exact congrArg ((a : A)*·) (ih hv)

def halfCornerTrace (τ : A →ₗ[ℂ] ℂ) : Corner hp →ₗ[ℂ] ℂ :=
  (2 : ℂ) • τ.comp (cornerSubalgebra hp).toSubmodule.subtype

@[simp] lemma halfCornerTrace_apply (τ : A →ₗ[ℂ] ℂ) (a : Corner hp) :
    halfCornerTrace hp τ a=2*τ (a : A) := rfl

lemma halfCornerTrace_tracial (τ : A →ₗ[ℂ] ℂ)
    (htr : ∀ a b : A, τ (a*b)=τ (b*a)) (a b : Corner hp) :
    halfCornerTrace hp τ (a*b)=halfCornerTrace hp τ (b*a) := by
  simp only [halfCornerTrace_apply,corner_mul,htr]

lemma halfCornerTrace_star (τ : A →ₗ[ℂ] ℂ)
    (hstar : ∀ a : A, τ (star a)=star (τ a)) (a : Corner hp) :
    halfCornerTrace hp τ (star a)=star (halfCornerTrace hp τ a) := by
  simp only [halfCornerTrace_apply,corner_star,hstar,star_mul,star_ofNat]
  exact mul_comm _ _

end Kadison

namespace Kadison.DihedralCorner

open FreeMoments

variable {A : Type*} [CStarAlgebra A]

variable {ι : Type*} {S : ι → StarSubalgebra ℂ A} (τ : A →ₗ[ℂ] ℂ)

variable (htr : ∀ a b : A, τ (a*b)=τ (b*a)) (hfree : Free S τ)

variable (d s : unitary A) (i j : ι) (hij : i≠j)

variable (hd : (d : A)∈S i) (hs : (s : A)∈S j)
  (hd0 : τ (d : A)=0) (hs0 : τ (s : A)=0)

variable {p : A} (hp : IsStarProjection p) (hpd : p*(d : A)=p)

include htr hfree hij hd hs hd0 hs0 hpd in
theorem corner_cosine_pair_moment (v : List (Corner hp × ℕ)) (hne : v≠[])
    (hD : ∀ x∈v, (x.1 : A)∈S i)
    (h0 : ∀ x∈v, halfCornerTrace hp τ x.1=0) :
    halfCornerTrace hp τ ((v.map (fun x => x.1*cosine (d*s) hp (x.2+1))).prod)=0 := by
  let D : Letter S τ := ⟨i,d,hd,hd0⟩
  let F : Letter S τ := ⟨j,s,hs,hs0⟩
  have hc : ∀ x∈v, τ (x.1 : A)=0 := by
    intro x hx
    have h := h0 x hx
    simpa only [halfCornerTrace_apply,mul_eq_zero,OfNat.ofNat_ne_zero,false_or] using h
  let letters : List (Letter S τ × ℕ) := v.attach.map (fun x =>
    (⟨i,x.1.1,hD x.1 x.2,hc x.1 x.2⟩,x.1.2))
  have hletters : letters≠[] := by simp [letters,hne]
  have hcolor : ∀ x∈letters, x.1.color≠F.color := by
    intro x hx
    obtain ⟨y,_,rfl⟩ := List.mem_map.mp hx
    exact hij
  have had : ∀ x∈letters, x.1.val*D.val=x.1.val := by
    intro x hx
    obtain ⟨y,_,rfl⟩ := List.mem_map.mp hx
    change (y.1.1 : A)*(d : A)=(y.1.1 : A)
    rw [←y.1.1.property.2, mul_assoc, hpd, y.1.1.property.2]
  have hm := dihedral_cyclic_moment hfree F D hij letters hletters hcolor had
  have hl : (letters.map (fun x => x.1.val*(D.val*F.val)^(x.2+1))).prod =
      (v.map (fun x => (x.1 : A)*((d : A)*(s : A))^(x.2+1))).prod := by
    exact (congrArg List.prod List.map_map).trans
      (congrArg List.prod (List.attach_map_val
        (f := fun x : Corner hp × ℕ => (x.1 : A)*((d : A)*(s : A))^(x.2+1))))
  rw [hl] at hm
  have hprod : (((v.map (fun x => x.1*cosine (d*s) hp (x.2+1))).prod : Corner hp) : A) =
      (v.map (fun x => ((x.1*cosine (d*s) hp (x.2+1) : Corner hp) : A))).prod := by
    exact (corner_list_prod_coe hp _ (by simpa using hne)).trans
      (congrArg List.prod List.map_map)
  rw [halfCornerTrace_apply,hprod]
  have hv : (v.map (fun x => ((x.1*cosine (d*s) hp (x.2+1) : Corner hp) : A))) =
      v.map (fun x => (x.1 : A)*((d : A)*(s : A))^(x.2+1)*p) := by
    apply List.map_congr_left
    intro x hx
    change (x.1 : A)*(p*wave (d*s) (x.2+1)*p)=_
    rw [←mul_assoc, ←mul_assoc, x.1.property.2]
    have he : wave (d*s) (x.2+1)=((d : A)*(s : A))^(x.2+1) := by
      change (((d*s)^((x.2+1 : ℕ) : ℤ) : unitary A) : A)=_
      rw [zpow_natCast]
      simp only [SubmonoidClass.coe_pow,Submonoid.coe_mul]
    rw [he]
  change 2*τ ((v.map (fun x => ((x.1*cosine (d*s) hp (x.2+1) : Corner hp) : A))).prod)=0
  rw [hv]
  have hr := CornerMoments.traceremove p τ htr
    (v.map (fun x => ((x.1 : A),((d : A)*(s : A))^(x.2+1))))
    (by simpa using hne) (by
      intro x hx; obtain ⟨y,_,rfl⟩ := List.mem_map.mp hx; exact y.1.property.1)
  simp only [List.map_map,Function.comp_def] at hr
  rw [hr,hm,mul_zero]

end Kadison.DihedralCorner

namespace Kadison.FreeMoments

variable {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]

variable {S : Bool → StarSubalgebra ℂ A} {τ : A →ₗ[ℂ] ℂ}

def flattenPairs (v : List (Letter S τ × Letter S τ)) : List (Letter S τ) :=
  v.flatMap (fun x => [x.1,x.2])

@[simp] lemma flattenPairs_nil : flattenPairs ([] : List (Letter S τ × Letter S τ))=[] := rfl

@[simp] lemma flattenPairs_cons (x : Letter S τ × Letter S τ) (v) :
    flattenPairs (x::v)=x.1::x.2::flattenPairs v := rfl

lemma word_flattenPairs (v : List (Letter S τ × Letter S τ)) :
    word (flattenPairs v)=(v.map (fun x => x.1.val*x.2.val)).prod := by
  induction v with
  | nil => rfl
  | cons x v ih => simp only [flattenPairs_cons, word_cons, ih, List.map_cons,
      List.prod_cons, mul_assoc]

lemma flattenPairs_parse (a b : Letter S τ) (m : List (Letter S τ))
    (ha : a.color=false) (hb : b.color=true) (hw : Reduced (a::m++[b])) :
    ∃ v : List (Letter S τ × Letter S τ), v≠[] ∧
      flattenPairs v=a::m++[b] ∧ ∀ x∈v, x.1.color=false ∧ x.2.color=true := by
  induction hn : m.length using Nat.strong_induction_on generalizing a m with
  | h n ih =>
    cases m with
    | nil => exact ⟨[(a,b)],by simp,by rfl,by intro x hx; obtain rfl := List.mem_singleton.mp hx; exact ⟨ha,hb⟩⟩
    | cons c m =>
      have hc : c.color=true := by
        have hac : a.color≠c.color := hw.rel
        cases hcc : c.color <;> simp_all
      cases m with
      | nil =>
        have hcb : c.color≠b.color := hw.tail.rel
        exact (hcb (hc.trans hb.symm)).elim
      | cons d m =>
        have hd : d.color=false := by
          have hcd : c.color≠d.color := hw.tail.rel
          cases hdd : d.color <;> simp_all
        obtain ⟨v,hv,hvw,hvc⟩ := ih m.length (by simp at hn; omega) d m hd hw.tail.tail rfl
        refine ⟨(a,c)::v,by simp,?_,?_⟩
        · simp only [flattenPairs_cons, hvw, List.cons_append]
        · intro x hx
          rcases List.mem_cons.mp hx with rfl|hx
          · exact ⟨ha,hc⟩
          · exact hvc x hx

variable (h1 : τ 1=1) (htr : ∀ a b : A, τ (a*b)=τ (b*a))
  (hstar : ∀ a : A, τ (star a)=star (τ a))

include h1 htr hstar in
theorem free_bool_of_pair_moments
    (hpair : ∀ v : List (Letter S τ × Letter S τ), v≠[] →
      (∀ x∈v, x.1.color=false ∧ x.2.color=true) →
      τ ((v.map (fun x => x.1.val*x.2.val)).prod)=0) : Free S τ := by
  apply free_of_different_endpoints S τ h1 htr
  intro a b m hw hab
  have hdir : ∀ (a b : Letter S τ) (m : List (Letter S τ)),
      a.color=false → b.color=true → Reduced (a::m++[b]) → τ (word (a::m++[b]))=0 := by
    intro a b m ha hb hw
    obtain ⟨v,hv,hvw,hvc⟩ := flattenPairs_parse a b m ha hb hw
    rw [←hvw,word_flattenPairs]
    exact hpair v hv hvc
  cases ha : a.color with
  | false =>
    have hb : b.color=true := by cases hb : b.color <;> simp_all
    exact hdir a b m ha hb hw
  | true =>
    have hb : b.color=false := by cases hb : b.color <;> simp_all
    have heq : reverseStar hstar (a::m++[b]) =
        b.conj hstar :: reverseStar hstar m ++ [a.conj hstar] := by
      simp [reverseStar]
    have hz := hdir (b.conj hstar) (a.conj hstar) (reverseStar hstar m) hb ha
      (by rw [←heq]; exact hw.reverseStar hstar)
    rw [←heq,word_reverseStar,hstar] at hz
    exact star_eq_zero.mp hz

omit [StarRing A] [StarModule ℂ A] in
lemma paired_vanish_on_spans (B : Set A) (a : List A) (φ : A →ₗ[ℂ] ℂ)
    (h : ∀ b : List A, List.Forall₂ (fun _ x => x∈B) a b →
      φ ((List.zipWith (·*·) a b).prod)=0) :
    ∀ b : List A, List.Forall₂ (fun _ x => x∈Submodule.span ℂ B) a b →
      φ ((List.zipWith (·*·) a b).prod)=0 := by
  induction a generalizing φ with
  | nil => intro b hb; cases hb; exact h [] .nil
  | cons a as ih =>
    intro b hb
    cases hb with
    | cons hx hbs =>
      rename_i x xs
      let ψ : A →ₗ[ℂ] ℂ := φ.comp (LinearMap.mulLeft ℂ (a*x))
      apply ih ψ ?_ xs hbs
      intro ys hys
      change φ ((a*x)*(List.zipWith (·*·) as ys).prod)=0
      induction hx using Submodule.span_induction with
      | mem x hx => exact h (x::ys) (.cons hx hys)
      | zero => simp
      | add x y _ _ hx hy => simp only [mul_add, add_mul, map_add, hx,hy,add_zero]
      | smul c x _ hx => simp only [mul_smul_comm,smul_mul_assoc,map_smul,hx,smul_zero]

end Kadison.FreeMoments

namespace Kadison.FreeMoments

lemma pair_generators_witness {A I : Type*} (c : I → A) {a b : List A}
    (hb : List.Forall₂ (fun _ x => x∈Set.range c) a b) :
    ∃ v : List (A×I), v.map Prod.fst=a ∧ v.map (fun x => c x.2)=b := by
  induction hb with
  | nil => exact ⟨[],rfl,rfl⟩
  | @cons a b as bs hb hbs ih =>
    obtain ⟨i,rfl⟩ := hb
    obtain ⟨v,rfl,rfl⟩ := ih
    exact ⟨(a,i)::v,rfl,rfl⟩

lemma zipWith_same_maps {A B C E : Type*} (m : B → C → E) (f : A → B) (g : A → C)
    (v : List A) : List.zipWith m (v.map f) (v.map g) = v.map (fun x => m (f x) (g x)) := by
  induction v with
  | nil => rfl
  | cons a v ih => simp only [List.map_cons,List.zipWith_cons_cons,ih]

variable {A : Type*} [Ring A] [Algebra ℂ A]

lemma pairs_vanish_on_second_span {I : Type*} (F : Set A) (c : I → A)
    (φ : A →ₗ[ℂ] ℂ)
    (h : ∀ v : List (A×I), v≠[] → (∀ x∈v,x.1∈F) →
      φ ((v.map (fun x => x.1*c x.2)).prod)=0)
    (v : List (A×A)) (hne : v≠[])
    (hF : ∀ x∈v,x.1∈F) (hB : ∀ x∈v,x.2∈Submodule.span ℂ (Set.range c)) :
    φ ((v.map (fun x => x.1*x.2)).prod)=0 := by
  have hz := paired_vanish_on_spans (Set.range c) (v.map Prod.fst) φ (fun b hb => ?_)
    (v.map Prod.snd) (by
      rw [List.forall₂_map_left_iff,List.forall₂_map_right_iff,List.forall₂_same]
      exact hB)
  · simpa only [zipWith_same_maps] using hz
  obtain ⟨w,hw,hwb⟩ := pair_generators_witness c hb
  have hwne : w≠[] := by
    intro he; simp only [he,List.map_nil] at hw
    exact hne (List.map_eq_nil_iff.mp hw.symm)
  have hwF : ∀ x∈w,x.1∈F := by
    intro x hx
    have hm : x.1∈v.map Prod.fst := hw ▸ List.mem_map_of_mem hx
    obtain ⟨y,hy,hxy⟩ := List.mem_map.mp hm
    exact hxy ▸ hF y hy
  rw [←hw,←hwb,zipWith_same_maps]
  exact h w hwne hwF

end Kadison.FreeMoments

namespace Kadison.DihedralCorner

open FreeMoments

variable {A : Type*} [CStarAlgebra A]

variable {ι : Type*} {S : ι → StarSubalgebra ℂ A} (τ : A →ₗ[ℂ] ℂ)

variable (h1 : τ 1=1) (htr : ∀ a b : A, τ (a*b)=τ (b*a))
  (hstar : ∀ a : A, τ (star a)=star (τ a)) (hfree : Free S τ)

variable (d s : unitary A) (i j : ι) (hij : i≠j)

variable (hd : (d : A)∈S i) (hs : (s : A)∈S j)
  (hd0 : τ (d : A)=0) (hs0 : τ (s : A)=0)

variable (hr : MulAut.conj d (d*s)=(d*s)⁻¹) (hd2 : (d : A)*(d : A)=1)

variable {p : A} (hp : IsStarProjection p) (hpform : p=(1/2 : ℂ) • (1+(d : A)))
  (hpd : p*(d : A)=p) (hdp : (d : A)*p=p)

include h1 hd0 hpform in
lemma halfCornerTrace_one : halfCornerTrace hp τ 1=1 := by
  simp only [halfCornerTrace_apply,corner_one,hpform,map_smul,map_add,h1,hd0]
  norm_num

include htr hfree hij hd hs hd0 hs0 hr hd2 hpform hpd hdp in
lemma cosine_centered (n : ℤ) (hn : n≠0) : halfCornerTrace hp τ (cosine (d*s) hp n)=0 := by
  have hpos (m : ℕ) : halfCornerTrace hp τ (cosine (d*s) hp (m+1))=0 := by
    rw [halfCornerTrace_apply,
      cosine_positive_centered τ htr hfree d s i j hij hd hs hd0 hs0 hp hpform hd2,mul_zero]
  cases n with
  | ofNat n =>
    cases n with
    | zero => exact (hn rfl).elim
    | succ m => exact hpos m
  | negSucc m =>
    change halfCornerTrace hp τ (cosine (d*s) hp (-((m+1 : ℕ) : ℤ)))=0
    rw [cosine_neg (d*s) d hr hp hpd hdp]
    exact hpos m

def cornerPairFactors (hpD : p∈S i) : Bool → StarSubalgebra ℂ (Corner hp) :=
  fun b => if b then cosineAlgebra (d*s) d hr hp hpform hdp else cornerFactor hp (S i) hpD

include h1 htr hstar hfree hij hd hs hd0 hs0 hd2 hpd in
theorem corner_cosine_free (hpD : p∈S i) :
    Free (cornerPairFactors (S:=S) d s i hr hp hpform hdp hpD) (halfCornerTrace hp τ) := by
  let R := cornerPairFactors (S:=S) d s i hr hp hpform hdp hpD
  have hτ1 := halfCornerTrace_one τ h1 d hd0 hp hpform
  have hτ0 := cosine_centered τ htr hfree d s i j hij hd hs hd0 hs0 hr hd2 hp hpform hpd hdp
  apply free_bool_of_pair_moments (S := R) (τ := halfCornerTrace hp τ) hτ1
    (halfCornerTrace_tracial hp τ htr) (halfCornerTrace_star hp τ hstar)
  intro v hv hcolor
  let F : Set (Corner hp) := {a | (a : A)∈S i ∧ halfCornerTrace hp τ a=0}
  have hD : ∀ x∈v, x.1.val∈F := by
    intro x hx
    have hm := x.1.mem
    rw [(hcolor x hx).1] at hm
    exact ⟨hm,x.1.centered⟩
  have hB : ∀ x∈v, x.2.val∈Submodule.span ℂ (positiveCosines (d*s) hp) := by
    intro x hx
    have hm := x.2.mem
    rw [(hcolor x hx).2] at hm
    exact centered_cosineAlgebra_span (d*s) d hr hp hpform hpd hdp
      (halfCornerTrace hp τ) hτ1 hτ0 hm x.2.centered
  have hz := pairs_vanish_on_second_span F (fun n : ℕ => cosine (d*s) hp (n+1))
    (halfCornerTrace hp τ)
    (fun w hw hwF => corner_cosine_pair_moment τ htr hfree d s i j hij hd hs hd0 hs0 hp hpd
      w hw (fun x hx => (hwF x hx).1) (fun x hx => (hwF x hx).2))
    (v.map (fun x => (x.1.val,x.2.val))) (by simpa using hv) (by
      intro x hx; obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx; exact hD y hy) (by
      intro x hx; obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx; exact hB y hy)
  simpa only [List.map_map,Function.comp_def] using hz

end Kadison.DihedralCorner

end

end
end

end OAI
