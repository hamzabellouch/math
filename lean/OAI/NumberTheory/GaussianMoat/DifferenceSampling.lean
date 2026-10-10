import OAI.NumberTheory.GaussianMoat.WalkGeometry

namespace OAI

namespace GaussianMoat

noncomputable def walkSegment (z : ℕ → GaussianInt) (n : ℕ) : Finset GaussianInt :=
  (Finset.range (n+1)).image z

noncomputable def differences (E : Finset GaussianInt) : Finset GaussianInt :=
  (E ×ˢ E).image (fun p => p.1-p.2)

@[simp] theorem mem_walkSegment (z : ℕ → GaussianInt) (n : ℕ) (w : GaussianInt) :
    w ∈ walkSegment z n ↔ ∃ i ≤ n, z i = w := by
  simp [walkSegment,Finset.mem_image]

@[simp] theorem mem_differences (E : Finset GaussianInt) (w : GaussianInt) :
    w ∈ differences E ↔ ∃ a ∈ E, ∃ b ∈ E, a-b = w := by
  simp [differences,Finset.mem_image,Prod.exists,and_assoc]

theorem card_le_card_differences {E : Finset GaussianInt} (hE : E.Nonempty) :
    E.card ≤ (differences E).card := by
  classical
  obtain ⟨a,ha⟩ := hE
  have hs : E.image (fun b => b-a) ⊆ differences E := by
    intro w hw
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hw
    exact mem_differences E (b-a) |>.mpr ⟨b,hb,a,ha,rfl⟩
  have hi : Function.Injective (fun b : GaussianInt => b-a) := sub_left_injective
  rw [← Finset.card_image_of_injective E hi]
  exact Finset.card_le_card hs

theorem walkSegment_dist_le (z : ℕ → GaussianInt) {n : ℕ} {D : ℝ} (hD : 0 ≤ D)
    (hz : ∀ i < n, dist (z i:ℂ) (z (i+1):ℂ) ≤ D) {i j : ℕ} (hi : i ≤ n) (hj : j ≤ n) :
    dist (z i:ℂ) (z j:ℂ) ≤ D*n := by
  wlog hij : i ≤ j generalizing i j
  · rw [dist_comm]
    exact this hj hi (by omega)
  have h := dist_le_Ico_sum_of_dist_le (f := fun k => (z k:ℂ)) hij
    (d := fun _ => D) (fun {k} _ hk => hz k (lt_of_lt_of_le hk hj))
  simp only [Finset.sum_const,Nat.card_Ico,nsmul_eq_mul] at h
  calc
    dist (z i:ℂ) (z j:ℂ) ≤ (j-i:ℕ)*D := h
    _ ≤ (n:ℝ)*D := mul_le_mul_of_nonneg_right (by exact_mod_cast (show j-i ≤ n by omega)) hD
    _ = D*n := mul_comm _ _

def joinedPath (z : ℕ → GaussianInt) (t : ℕ) (i : ℕ) : GaussianInt :=
  z (Nat.dist t i)-z t

@[simp] theorem joinedPath_zero (z : ℕ → GaussianInt) (t : ℕ) : joinedPath z t 0 = 0 := by
  simp [joinedPath,Nat.dist]

@[simp] theorem joinedPath_end (z : ℕ → GaussianInt) (t s : ℕ) :
    joinedPath z t (t+s) = z s-z t := by simp [joinedPath,Nat.dist]

theorem joinedPath_step (z : ℕ → GaussianInt) {n t s : ℕ} (ht : t ≤ n) (hs : s ≤ n)
    {D : ℝ} (hz : ∀ i < n, dist (z i:ℂ) (z (i+1):ℂ) ≤ D) :
    ∀ i < t+s, dist (joinedPath z t i:ℂ) (joinedPath z t (i+1):ℂ) ≤ D := by
  intro i hi
  simp only [joinedPath,map_sub,dist_sub_right]
  by_cases hit : i < t
  · have he : Nat.dist t i = Nat.dist t (i+1)+1 := by simp only [Nat.dist]; omega
    rw [he,dist_comm]
    exact hz _ (by simp only [Nat.dist]; omega)
  · have he : Nat.dist t (i+1) = Nat.dist t i+1 := by simp only [Nat.dist]; omega
    rw [he]
    exact hz _ (by simp only [Nat.dist]; omega)

theorem differences_card_of_triangle (z : ℕ → GaussianInt) {n t s u : ℕ}
    (ht : t ≤ n) (hs : s ≤ n) (hu : u ≤ n) {D : ℝ} (hD : 0 ≤ D)
    (hz : ∀ i < n, dist (z i:ℂ) (z (i+1):ℂ) ≤ D)
    (hab : (z s-z t).re*(z u-z t).im-(z s-z t).im*(z u-z t).re ≠ 0) :
    ((z s-z t).re*(z u-z t).im-(z s-z t).im*(z u-z t).re).natAbs ≤
      (differences (walkSegment z n)).card * (latticeBall (4*D)).card := by
  have hts : 0 < t+s := by
    by_contra hh
    have ht0 : t=0 := by omega
    have hs0 : s=0 := by omega
    simp [ht0,hs0] at hab
  have htu : 0 < t+u := by
    by_contra hh
    have ht0 : t=0 := by omega
    have hu0 : u=0 := by omega
    simp [ht0,hu0] at hab
  apply lattice_path_difference_card (joinedPath z t) (joinedPath z t) hts htu
    (z s-z t) (z u-z t) (joinedPath_zero z t) (joinedPath_zero z t)
    (joinedPath_end z t s) (joinedPath_end z t u) hab hD
    (joinedPath_step z ht hs hz) (joinedPath_step z ht hu hz)
  intro i hi j hj
  apply (mem_differences _ _).mpr
  refine ⟨z (Nat.dist t i),(mem_walkSegment _ _ _).mpr ⟨_,?_,rfl⟩,
    z (Nat.dist t j),(mem_walkSegment _ _ _).mpr ⟨_,?_,rfl⟩,?_⟩
  · simp only [Nat.dist]; omega
  · simp only [Nat.dist]; omega
  · simp only [joinedPath]; ring

noncomputable def diameterRotation (a : ℂ) : ℂ := star a / (‖a‖:ℂ)

theorem diameterRotation_norm {a : ℂ} (ha : a ≠ 0) : ‖diameterRotation a‖ = 1 := by
  simp [diameterRotation,Complex.norm_real,norm_ne_zero_iff.mpr ha]

theorem diameterRotation_mul (a : ℂ) : diameterRotation a*a = (‖a‖:ℂ) := by
  by_cases ha : a=0
  · simp [ha,diameterRotation]
  have hn : (‖a‖:ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr ha
  have hm : star a*a = (‖a‖:ℂ)^2 := Complex.conj_mul' a
  rw [diameterRotation,div_mul_eq_mul_div,hm]
  field_simp

theorem diameter_rectangle {a v : ℂ} (ha : a ≠ 0) (hv : ‖v‖ ≤ ‖a‖)
    (hva : ‖v-a‖ ≤ ‖a‖) :
    0 ≤ (diameterRotation a*v).re ∧ (diameterRotation a*v).re ≤ ‖a‖ ∧
      |(diameterRotation a*v).im| ≤ ‖a‖ := by
  let u := diameterRotation a*v
  have hn : ‖u‖ ≤ ‖a‖ := by simpa [u,norm_mul,diameterRotation_norm ha] using hv
  have hna : ‖u-(‖a‖:ℂ)‖ ≤ ‖a‖ := by
    rw [← diameterRotation_mul a,← mul_sub]
    simpa [norm_mul,diameterRotation_norm ha] using hva
  have hr := Complex.abs_re_le_norm u
  have hi := Complex.abs_im_le_norm u
  have hra := Complex.abs_re_le_norm (u-(‖a‖:ℂ))
  simp only [Complex.sub_re,Complex.ofReal_re] at hra
  have hl := (abs_le.mp (hra.trans hna)).1
  exact ⟨by dsimp [u] at *; linarith, (le_abs_self u.re).trans (hr.trans hn), hi.trans hn⟩

theorem diameter_height (a b : GaussianInt) :
    |((a.re*b.im-a.im*b.re:ℤ):ℝ)| =
      ‖(a:ℂ)‖*|(diameterRotation (a:ℂ)*(b:ℂ)).im| := by
  by_cases ha : a=0
  · simp [ha,diameterRotation]
  have hna : ‖(a:ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr (by simpa using ha)
  have he : (diameterRotation (a:ℂ)*(b:ℂ)).im =
      ((a.re:ℝ)*(b.im:ℝ)-(a.im:ℝ)*(b.re:ℝ))/‖(a:ℂ)‖ := by
    simp only [diameterRotation,div_mul_eq_mul_div,Complex.div_ofReal_im,
      Complex.mul_im,Complex.star_def,Complex.conj_re,Complex.conj_im,
      ← GaussianInt.intCast_re,← GaussianInt.intCast_im]
    ring
  rw [he,abs_div,abs_of_nonneg (norm_nonneg (a:ℂ))]
  push_cast
  field_simp

theorem walk_many_differences (z : ℕ → GaussianInt) {n : ℕ} (hn : 1 ≤ n)
    (hinj : Function.Injective z) {D : ℝ} (hD : 1 ≤ D)
    (hz : ∀ i < n, dist (z i:ℂ) (z (i+1):ℂ) ≤ D) :
    ∃ (R W : ℝ) (e c : ℂ), 1 ≤ W ∧ W ≤ R ∧ ‖e‖ = 1 ∧
      (∀ p ∈ walkSegment z n, 0 ≤ (e*((p:ℂ)-c)).re ∧
        (e*((p:ℂ)-c)).re ≤ R ∧ |(e*((p:ℂ)-c)).im| ≤ W) ∧
      (n:ℝ) ≤ 18*(R*W) ∧ R*W ≤ D^2*(n:ℝ)^2 ∧
      R*W ≤ max D ((latticeBall (4*D)).card:ℝ)*(differences (walkSegment z n)).card := by
  classical
  let I := Finset.range (n+1)
  have hI : I.Nonempty := ⟨0,by simp [I]⟩
  obtain ⟨⟨t,s⟩,hts,hmax⟩ := Finset.exists_max_image (I ×ˢ I)
    (fun q => dist (z q.1:ℂ) (z q.2:ℂ)) (hI.product hI)
  have ht : t ≤ n := by simpa [I] using (Finset.mem_product.mp hts).1
  have hs : s ≤ n := by simpa [I] using (Finset.mem_product.mp hts).2
  let a := z s-z t
  let R := ‖(a:ℂ)‖
  have hdiam : ∀ i ≤ n, ∀ j ≤ n, dist (z i:ℂ) (z j:ℂ) ≤ R := by
    intro i hi j hj
    have h := hmax (i,j) (by simp [I,hi,hj])
    simpa [R,a,map_sub,← dist_eq_norm,dist_comm] using h
  have hR : 1 ≤ R := (lattice_dist_ge_one (hinj.ne (by omega : 0 ≠ 1))).trans (hdiam 0 (by omega) 1 hn)
  have ha : a ≠ 0 := by intro hh; simp [R,hh] at hR; linarith
  have hac : (a:ℂ) ≠ 0 := by simpa using ha
  let e := diameterRotation (a:ℂ)
  let c := (z t:ℂ)
  have he : ‖e‖ = 1 := diameterRotation_norm hac
  have hr : ∀ i ≤ n, 0 ≤ (e*((z i:ℂ)-c)).re ∧
      (e*((z i:ℂ)-c)).re ≤ R ∧ |(e*((z i:ℂ)-c)).im| ≤ R := by
    intro i hi
    have hv : ‖(z i:ℂ)-c‖ ≤ ‖(a:ℂ)‖ := by simpa only [← dist_eq_norm] using hdiam i hi t ht
    have hva : ‖((z i:ℂ)-c)-(a:ℂ)‖ ≤ ‖(a:ℂ)‖ := by
      have hh : ((z i:ℂ)-c)-(a:ℂ) = (z i:ℂ)-(z s:ℂ) := by simp [a,c]
      rw [hh,← dist_eq_norm]
      exact hdiam i hi s hs
    exact diameter_rectangle hac hv hva
  obtain ⟨u,hu,humax⟩ := Finset.exists_max_image I
    (fun i => |(e*((z i:ℂ)-c)).im|) hI
  have hu' : u ≤ n := by simpa [I] using hu
  let W := max 1 |(e*((z u:ℂ)-c)).im|
  have hW : 1 ≤ W := le_max_left _ _
  have hWR : W ≤ R := max_le hR (hr u hu').2.2
  have hrect : ∀ p ∈ walkSegment z n, 0 ≤ (e*((p:ℂ)-c)).re ∧
      (e*((p:ℂ)-c)).re ≤ R ∧ |(e*((p:ℂ)-c)).im| ≤ W := by
    intro p hp
    obtain ⟨i,hi,rfl⟩ := (mem_walkSegment _ _ _).mp hp
    exact ⟨(hr i hi).1,(hr i hi).2.1,(humax i (by simpa [I] using hi)).trans (le_max_right _ _)⟩
  have hcard : (walkSegment z n).card = n+1 := by
    rw [walkSegment,Finset.card_image_of_injective _ hinj,Finset.card_range]
  have hcount : (n:ℝ)+1 ≤ 18*R*W := by
    have h := lattice_rectangle_card (walkSegment z n) he hR hW hrect
    simpa only [hcard,Nat.cast_add,Nat.cast_one] using h
  have hRD : R ≤ D*n := by
    simpa only [R,a,map_sub,← dist_eq_norm] using walkSegment_dist_le z (by linarith) hz hs ht
  have hAupper : R*W ≤ D^2*(n:ℝ)^2 := by
    have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg _
    have hm := mul_le_mul hRD hRD (by linarith : 0 ≤ R) (by positivity : 0 ≤ D*n)
    have hw := mul_le_mul_of_nonneg_left hWR (by linarith : 0 ≤ R)
    nlinarith
  refine ⟨R,W,e,c,hW,hWR,he,hrect,by nlinarith,hAupper,?_⟩
  have hdif := card_le_card_differences (E := walkSegment z n)
    ⟨z 0,(mem_walkSegment _ _ _).mpr ⟨0,by omega,rfl⟩⟩
  have hcountdif : (n:ℝ)+1 ≤ ((differences (walkSegment z n)).card:ℝ) := by
    rw [hcard] at hdif
    exact_mod_cast hdif
  by_cases hthin : |(e*((z u:ℂ)-c)).im| ≤ 1
  · have hWeq : W = 1 := max_eq_left hthin
    rw [hWeq,mul_one]
    have hdn : D*(n:ℝ) ≤ D*((differences (walkSegment z n)).card:ℝ) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    exact (hRD.trans hdn).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · have hWeq : W = |(e*((z u:ℂ)-c)).im| := max_eq_right (by linarith)
    let b := z u-z t
    have hdet : |((a.re*b.im-a.im*b.re:ℤ):ℝ)| = R*W := by
      rw [diameter_height,hWeq]
      simp only [R,e,b,map_sub,c]
    have hab : a.re*b.im-a.im*b.re ≠ 0 := by
      intro hh
      rw [hh,Int.cast_zero,abs_zero] at hdet
      have : 0 < R*W := mul_pos (by linarith) (by linarith)
      linarith
    have hcd := differences_card_of_triangle z ht hs hu' (by linarith) hz hab
    have hcd' : |((a.re*b.im-a.im*b.re:ℤ):ℝ)| ≤
        ((differences (walkSegment z n)).card:ℝ)*((latticeBall (4*D)).card:ℝ) := by
      have hh : ((a.re*b.im-a.im*b.re).natAbs:ℝ) ≤
          ((differences (walkSegment z n)).card:ℝ)*((latticeBall (4*D)).card:ℝ) := by
        exact_mod_cast hcd
      simpa only [Nat.cast_natAbs,Int.cast_abs] using hh
    rw [hdet] at hcd'
    calc
      R*W ≤ ((differences (walkSegment z n)).card:ℝ)*((latticeBall (4*D)).card:ℝ) := hcd'
      _ = ((latticeBall (4*D)).card:ℝ)*((differences (walkSegment z n)).card:ℝ) := mul_comm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

end GaussianMoat

end OAI
