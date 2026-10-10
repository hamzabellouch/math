import Mathlib
import OAI.NumberTheory.PrimePackets.AdelicScalar

namespace OAI

noncomputable section
open scoped TensorProduct RestrictedProduct Topology Pointwise MatrixGroups
open Matrix Module Filter Set
namespace PrimeDegreePackets.Adelic

lemma finite_matrix_integral_mul {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) RationalFiniteAdeles)
    (hA : ∀ i j p, A i j p ∈ rationalLocalIntegers p)
    (hB : ∀ i j p, B i j p ∈ rationalLocalIntegers p) :
    ∀ i j p, (A * B) i j p ∈ rationalLocalIntegers p := by
  intro i j p
  change (RestrictedProduct.evalRingHom (fun p : Nat.Primes => Padic p.val) p)
    ((A * B) i j) ∈ rationalLocalIntegers p
  rw [Matrix.mul_apply,map_sum]
  apply sum_mem
  intro k _
  rw [map_mul]
  exact (rationalLocalIntegers p).mul_mem (hA i k p) (hB k j p)

lemma integralFiniteGL_one (n : ℕ) : IntegralFiniteGL (1 : GL (Fin n) RationalFiniteAdeles) := by
  have h : ∀ i j p, (1 : Matrix (Fin n) (Fin n) RationalFiniteAdeles) i j p ∈
      rationalLocalIntegers p := by
    intro i j p
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  exact ⟨h,by simpa only [inv_one, Units.val_one] using h⟩

lemma integralFiniteGL_mul {n : ℕ} {g h : GL (Fin n) RationalFiniteAdeles}
    (hg : IntegralFiniteGL g) (hh : IntegralFiniteGL h) : IntegralFiniteGL (g * h) := by
  refine ⟨finite_matrix_integral_mul _ _ hg.1 hh.1,?_⟩
  rw [_root_.mul_inv_rev]
  exact finite_matrix_integral_mul _ _ hh.2 hg.2

lemma integralFiniteGL_inv {n : ℕ} {g : GL (Fin n) RationalFiniteAdeles}
    (hg : IntegralFiniteGL g) : IntegralFiniteGL g⁻¹ :=
  ⟨hg.2,by simpa only [inv_inv] using hg.1⟩

 
def integralFiniteGroup (n : ℕ) : Subgroup (GL (Fin n) RationalFiniteAdeles) where
  carrier := {g | IntegralFiniteGL g}
  one_mem' := integralFiniteGL_one n
  mul_mem' := integralFiniteGL_mul
  inv_mem' := integralFiniteGL_inv

abbrev AdelicPGL (n : ℕ) := Matrix.ProjGenLinGroup (Fin n) ℝ ×
  Matrix.ProjGenLinGroup (Fin n) RationalFiniteAdeles

def rationalProjectiveEmbedding (n : ℕ) : Matrix.ProjGenLinGroup (Fin n) ℚ →* AdelicPGL n :=
  (Matrix.ProjGenLinGroup.map (algebraMap ℚ ℝ)).prod
    (Matrix.ProjGenLinGroup.map rationalFiniteEmbedding)

def rationalProjectiveGroup (n : ℕ) : Subgroup (AdelicPGL n) :=
  (rationalProjectiveEmbedding n).range

def finiteProjectiveIntegral (n : ℕ) : Subgroup (AdelicPGL n) :=
  (⊥ : Subgroup (Matrix.ProjGenLinGroup (Fin n) ℝ)).prod
    ((integralFiniteGroup n).map Matrix.ProjGenLinGroup.mk)

 
abbrev AmbientQuotient (n : ℕ) := DoubleCoset.Quotient
  (rationalProjectiveGroup n : Set (AdelicPGL n)) (finiteProjectiveIntegral n)

def realAmbientPoint {n : ℕ} (h : Matrix.SpecialLinearGroup (Fin n) ℝ) : AmbientQuotient n :=
  DoubleCoset.mk (rationalProjectiveGroup n) (finiteProjectiveIntegral n)
    (Matrix.SpecialLinearGroup.toPGL h,1)

lemma specialLinear_toPGL_injective_odd {n : ℕ} (hodd : Odd n) :
    Function.Injective (Matrix.SpecialLinearGroup.toPGL (n := Fin n) (R := ℝ)) := by
  intro g h hgh
  obtain ⟨u,hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hgh
  have hpow : (u : ℝ) ^ n = 1 := by
    have hd := congrArg (fun A : GL (Fin n) ℝ => A.val.det) hu
    simpa using hd
  have hu1 : u = 1 := by
    apply Units.ext
    apply hodd.pow_injective
    simpa using hpow
  rw [hu1,map_one,mul_one] at hu
  exact Subtype.ext (congrArg Units.val hu)

lemma specialLinear_toPGL_surjective_odd {n : ℕ} (hodd : Odd n) :
    Function.Surjective (Matrix.SpecialLinearGroup.toPGL (n := Fin n) (R := ℝ)) := by
  intro g
  obtain ⟨h,rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
  have hroot (x : ℝ) : ∃ r : ℝ, x = r ^ n := by
    by_cases hx : 0 ≤ x
    · exact ⟨x ^ ((n : ℝ)⁻¹), (Real.rpow_inv_natCast_pow hx hodd.pos.ne').symm⟩
    · refine ⟨-((-x) ^ ((n : ℝ)⁻¹)), ?_⟩
      rw [hodd.neg_pow,Real.rpow_inv_natCast_pow (by linarith) hodd.pos.ne',neg_neg]
  obtain ⟨r,hr⟩ := hroot (h.val.det⁻¹)
  have hr0 : r ≠ 0 := by
    intro he
    rw [he,zero_pow hodd.pos.ne',inv_eq_zero] at hr
    exact h.det_ne_zero hr
  have hd : (r • h.val).det = 1 := by
    rw [Matrix.det_smul,Fintype.card_fin,← hr,inv_mul_cancel₀ h.det_ne_zero]
  refine ⟨⟨r • h.val,hd⟩,?_⟩
  apply Matrix.ProjGenLinGroup.mk_eq_mk_iff.mpr
  refine ⟨(Units.mk0 r hr0)⁻¹,?_⟩
  apply Units.ext
  change (r • h.val) * Matrix.scalar (Fin n) r⁻¹ = h.val
  change (r • h.val) * Matrix.diagonal (fun _ => r⁻¹) = h.val
  rw [← Matrix.smul_one_eq_diagonal,Matrix.mul_smul,Matrix.mul_one,smul_smul]
  simp [hr0]

lemma integralFiniteGL_scalar {n : ℕ} {z : RationalFiniteAdelesˣ}
    (hz : IntegralFiniteScalar z) : IntegralFiniteGL (GeneralLinearGroup.scalar (Fin n) z) := by
  have h (u : RationalFiniteAdelesˣ)
      (hu : ∀ p, u.val p ∈ rationalLocalIntegers p) :
      ∀ i j p, (GeneralLinearGroup.scalar (Fin n) u).val i j p ∈ rationalLocalIntegers p := by
    intro i j p
    by_cases hij : i = j
    · subst j
      simpa using hu p
    · simp [Matrix.scalar_apply,Matrix.diagonal_apply_ne _ hij]
  refine ⟨h z (fun p => (hz p).1),?_⟩
  rw [← map_inv]
  exact h z⁻¹ (fun p => (hz p).2)

lemma rational_gl_of_finite_integral {n : ℕ} (c : GL (Fin n) ℚ)
    (hc : IntegralFiniteGL (GeneralLinearGroup.map rationalFiniteEmbedding c)) :
    ∃ z : GL (Fin n) ℤ, GeneralLinearGroup.map (Int.castRingHom ℚ) z = c := by
  classical
  have hm (A : Matrix (Fin n) (Fin n) ℚ)
      (hA : ∀ i j p, rationalFiniteEmbedding (A i j) p ∈ rationalLocalIntegers p) :
      ∃ Z : Matrix (Fin n) (Fin n) ℤ, Z.map (Int.castRingHom ℚ) = A := by
    have he (i j : Fin n) : ∃ z : ℤ, (z : ℚ) = A i j := by
      apply rat_integral_of_padic_integral
      intro p hp
      exact hA i j ⟨p,hp⟩
    choose Z hZ using he
    exact ⟨Z,Matrix.ext (fun i j => hZ i j)⟩
  obtain ⟨Z,hZ⟩ := hm c.val hc.1
  have hci : ∀ i j p, rationalFiniteEmbedding ((c⁻¹).val i j) p ∈ rationalLocalIntegers p := by
    intro i j p
    have h := hc.2 i j p
    rw [← map_inv] at h
    exact h
  obtain ⟨W,hW⟩ := hm (c⁻¹).val hci
  have hinj : Function.Injective (fun A : Matrix (Fin n) (Fin n) ℤ =>
      A.map (Int.castRingHom ℚ)) := Matrix.map_injective (Int.cast_injective (α := ℚ))
  have hZW : Z * W = 1 := by
    apply hinj
    dsimp only
    rw [Matrix.map_mul,hZ,hW,Units.mul_inv]
    simp
  have hWZ : W * Z = 1 := by
    apply hinj
    dsimp only
    rw [Matrix.map_mul,hZ,hW,Units.inv_mul]
    simp
  exact ⟨⟨Z,W,hZW,hWZ⟩,Units.ext hZ⟩

lemma projective_integral_real_lift {n : ℕ} (hodd : Odd n) (z : GL (Fin n) ℤ) :
    ∃ s : SpecialLinearGroup (Fin n) ℤ,
      SpecialLinearGroup.toPGL (SpecialLinearGroup.map (Int.castRingHom ℝ) s) =
      ProjGenLinGroup.mk (GeneralLinearGroup.map (Int.castRingHom ℝ) z) := by
  rcases Int.units_eq_one_or (GeneralLinearGroup.det z) with hd | hd
  · have hd' : z.val.det = 1 := congrArg Units.val hd
    refine ⟨⟨z.val,hd'⟩,?_⟩
    apply congrArg ProjGenLinGroup.mk
    apply Units.ext
    rfl
  · have hd' : z.val.det = -1 := congrArg Units.val hd
    have hn : (-z.val).det = 1 := by
      rw [Matrix.det_neg,Fintype.card_fin,hodd.neg_one_pow,hd']
      norm_num
    refine ⟨⟨-z.val,hn⟩,?_⟩
    apply ProjGenLinGroup.mk_eq_mk_iff.mpr
    refine ⟨-1,Units.ext ?_⟩
    change (-z.val).map (Int.castRingHom ℝ) * Matrix.diagonal (fun _ => (-1 : ℝ)) =
      z.val.map (Int.castRingHom ℝ)
    rw [← Matrix.smul_one_eq_diagonal,Matrix.mul_smul,Matrix.mul_one]
    ext i j
    simp

lemma rational_projective_integral_lift {n : ℕ} (hodd : Odd n)
    (a : ProjGenLinGroup (Fin n) ℚ)
    (ha : ProjGenLinGroup.map rationalFiniteEmbedding a ∈
      (integralFiniteGroup n).map ProjGenLinGroup.mk) :
    ∃ s : SpecialLinearGroup (Fin n) ℤ,
      ProjGenLinGroup.map (algebraMap ℚ ℝ) a =
        SpecialLinearGroup.toPGL (SpecialLinearGroup.map (Int.castRingHom ℝ) s) := by
  obtain ⟨c,rfl⟩ := ProjGenLinGroup.mk_surjective a
  obtain ⟨h,hh,he⟩ := ha
  obtain ⟨u,hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp he.symm
  obtain ⟨q,z,hz,huq⟩ := finite_scalar_rational_integral u
  let d := c * GeneralLinearGroup.scalar (Fin n) q
  have hd : GeneralLinearGroup.map rationalFiniteEmbedding d =
      h * GeneralLinearGroup.scalar (Fin n) z⁻¹ := by
    apply mul_right_cancel (b := GeneralLinearGroup.scalar (Fin n) z)
    rw [mul_assoc,← map_mul,inv_mul_cancel,map_one,mul_one]
    rw [← hu,huq,map_mul]
    simp only [map_mul,GeneralLinearGroup.map_scalar,mul_assoc]
    rfl
  obtain ⟨Z,hZ⟩ := rational_gl_of_finite_integral d (by
    rw [hd]
    exact integralFiniteGL_mul hh (integralFiniteGL_inv (integralFiniteGL_scalar hz)))
  obtain ⟨s,hs⟩ := projective_integral_real_lift hodd Z
  refine ⟨s,?_⟩
  rw [hs]
  have hmap : GeneralLinearGroup.map (Int.castRingHom ℝ) Z =
      GeneralLinearGroup.map (algebraMap ℚ ℝ) d := by
    rw [← hZ]
    apply Units.ext
    ext i j
    simp
  rw [hmap]
  simp [d,GeneralLinearGroup.map_scalar]

lemma integralFiniteGL_int_matrix {n : ℕ} (z : GL (Fin n) ℤ) :
    IntegralFiniteGL (GeneralLinearGroup.map rationalFiniteEmbedding
      (GeneralLinearGroup.map (Int.castRingHom ℚ) z)) := by
  have h (u : GL (Fin n) ℤ) : ∀ i j p,
      (GeneralLinearGroup.map rationalFiniteEmbedding
        (GeneralLinearGroup.map (Int.castRingHom ℚ) u)).val i j p ∈ rationalLocalIntegers p := by
    intro i j p
    change (((u.val i j : ℤ) : ℚ) : Padic p.val) ∈ rationalLocalIntegers p
    rw [Rat.cast_intCast]
    exact intCast_mem (rationalLocalIntegers p) (u.val i j)
  refine ⟨h z,?_⟩
  simpa only [map_inv] using h z⁻¹

lemma realAmbientPoint_eq_iff {n : ℕ} (hodd : Odd n) (g h : G n) :
    realAmbientPoint g = realAmbientPoint h ↔
      (QuotientGroup.rightRel (integralGroup n)) g h := by
  rw [realAmbientPoint,realAmbientPoint,DoubleCoset.eq,QuotientGroup.rightRel_apply]
  constructor
  · rintro ⟨a,⟨a,rfl⟩,k,hk,he⟩
    have hk1 : k.1 = 1 := hk.1
    have hk2 : k.2 ∈ (integralFiniteGroup n).map ProjGenLinGroup.mk := hk.2
    have hf : ProjGenLinGroup.map rationalFiniteEmbedding a * k.2 = 1 := by
      simpa [rationalProjectiveEmbedding] using (congrArg Prod.snd he).symm
    have ha : ProjGenLinGroup.map rationalFiniteEmbedding a ∈
        (integralFiniteGroup n).map ProjGenLinGroup.mk := by
      rw [eq_inv_of_mul_eq_one_left hf]
      exact Subgroup.inv_mem _ hk2
    obtain ⟨s,hs⟩ := rational_projective_integral_lift hodd a ha
    have hr : h = SpecialLinearGroup.map (Int.castRingHom ℝ) s * g := by
      apply specialLinear_toPGL_injective_odd hodd
      rw [map_mul]
      simpa [rationalProjectiveEmbedding,hk1,hs] using congrArg Prod.fst he
    rw [hr,mul_assoc,mul_inv_cancel,mul_one]
    exact ⟨s,rfl⟩
  · rintro ⟨s,hs⟩
    let a := ProjGenLinGroup.mk
      (GeneralLinearGroup.map (Int.castRingHom ℚ) (SpecialLinearGroup.toGL s))
    refine ⟨rationalProjectiveEmbedding n a,⟨a,rfl⟩,
      (1,(ProjGenLinGroup.map rationalFiniteEmbedding a)⁻¹),?_,?_⟩
    · constructor
      · rfl
      · apply Subgroup.inv_mem
        exact ⟨_,integralFiniteGL_int_matrix (SpecialLinearGroup.toGL s),rfl⟩
    · apply Prod.ext
      · change SpecialLinearGroup.toPGL h =
          ProjGenLinGroup.map (algebraMap ℚ ℝ) a * SpecialLinearGroup.toPGL g * 1
        rw [mul_one]
        have ha : ProjGenLinGroup.map (algebraMap ℚ ℝ) a =
            SpecialLinearGroup.toPGL (SpecialLinearGroup.map (Int.castRingHom ℝ) s) := by
          apply congrArg ProjGenLinGroup.mk
          apply Units.ext
          ext i j
          simp
        rw [ha,← map_mul,hs]
        congr 1
        group
      · simp [rationalProjectiveEmbedding]

lemma realAmbientPoint_surjective {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (hodd : Odd n) (hn : finrank ℚ K = n) (b : Basis (Fin n) ℚ K) :
    Function.Surjective (realAmbientPoint (n := n)) := by
  intro x
  induction x using Quotient.inductionOn with
  | h a =>
    obtain ⟨f,hf⟩ := ProjGenLinGroup.mk_surjective a.2
    obtain ⟨c,hc⟩ := finite_matrix_rational_reduction hn b f
    let q := ProjGenLinGroup.mk c
    let k := ProjGenLinGroup.map rationalFiniteEmbedding q * a.2
    have hk : k ∈ (integralFiniteGroup n).map ProjGenLinGroup.mk := by
      refine ⟨GeneralLinearGroup.map rationalFiniteEmbedding c * f,hc,?_⟩
      simp [k,q,hf]
    obtain ⟨h,hh⟩ := specialLinear_toPGL_surjective_odd hodd
      (ProjGenLinGroup.map (algebraMap ℚ ℝ) q * a.1)
    refine ⟨h,?_⟩
    apply Eq.symm
    apply DoubleCoset.eq.mpr
    refine ⟨rationalProjectiveEmbedding n q,⟨q,rfl⟩,(1,k⁻¹),⟨rfl,Subgroup.inv_mem _ hk⟩,?_⟩
    apply Prod.ext
    · simpa [realAmbientPoint,rationalProjectiveEmbedding] using hh
    · change (1 : ProjGenLinGroup (Fin n) RationalFiniteAdeles) = k * k⁻¹
      simp

 
theorem ambient_quotient_equiv {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (hodd : Odd n) (hn : finrank ℚ K = n) (b : Basis (Fin n) ℚ K) :
    ∃ e : PrimeDegreePackets.X n ≃ AmbientQuotient n,
      ∀ h : PrimeDegreePackets.G n, e (Quotient.mk _ h) = realAmbientPoint h := by
  let f : X n → AmbientQuotient n := Quotient.lift realAmbientPoint
    (fun g h hgh => (realAmbientPoint_eq_iff hodd g h).mpr hgh)
  have hi : Function.Injective f := by
    intro x y
    induction x using Quotient.inductionOn with
    | h g =>
      induction y using Quotient.inductionOn with
      | h h =>
        intro he
        exact Quotient.sound ((realAmbientPoint_eq_iff hodd g h).mp he)
  have hs : Function.Surjective f := by
    intro x
    obtain ⟨h,rfl⟩ := realAmbientPoint_surjective hodd hn b x
    exact ⟨Quotient.mk _ h,rfl⟩
  exact ⟨Equiv.ofBijective f ⟨hi,hs⟩,fun h => rfl⟩

end PrimeDegreePackets.Adelic

end

end OAI
