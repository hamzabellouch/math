import OAI.Geometry.UnitDistances.Sweep

namespace OAI

namespace PlanarUnitDistances.FiniteSampling
open Finset Classical

lemma avoiding_count {A : Type*} [Fintype A] (C : Finset A) (s : ℕ) :
    ((univ : Finset (Fin s → A)).filter (fun f => ∀ i, f i ∉ C)).card =
      (Fintype.card A-C.card)^s := by
  rw [← Fintype.card_subtype]
  rw [Fintype.card_congr (Equiv.subtypePiEquivPi (p := fun (_ : Fin s) a => a ∉ C))]
  rw [Fintype.card_fun,Fintype.card_subtype_compl]
  simp only [Fintype.card_fin,Fintype.card_coe]

lemma exists_hit {A I : Type*} [Fintype A] (K : Finset I) (C : I → Finset A)
    (s : ℕ) (h : (∑ i ∈ K, (Fintype.card A-(C i).card)^s) < (Fintype.card A)^s) :
    ∃ f : Fin s → A, ∀ i ∈ K, ∃ j, f j ∈ C i := by
  let bad : Finset (Fin s → A) := K.biUnion
    (fun i => univ.filter (fun f => ∀ j, f j ∉ C i))
  have hbad : bad.card < Fintype.card (Fin s → A) := by
    apply Finset.card_biUnion_le.trans_lt
    simpa only [avoiding_count,Fintype.card_fun,Fintype.card_fin] using h
  have hnot : ∃ f : Fin s → A, f ∉ bad := by
    by_contra hn
    push Not at hn
    have he : bad=univ := Finset.eq_univ_of_forall hn
    rw [he,Finset.card_univ] at hbad
    exact lt_irrefl _ hbad
  obtain ⟨f,hf⟩ := hnot
  refine ⟨f,?_⟩
  intro i hi
  by_contra hn
  push Not at hn
  exact hf (Finset.mem_biUnion.mpr ⟨i,hi,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩⟩)

lemma exists_hit_of_exponential {A I : Type*} [Fintype A]
    (hA : 0<Fintype.card A) (K : Finset I) (C : I → Finset A)
    {q : ℝ} (s : ℕ)
    (hC : ∀ i ∈ K, q ≤ ((C i).card : ℝ)/Fintype.card A)
    (hprob : (K.card : ℝ)*Real.exp (-(s : ℝ)*q)<1) :
    ∃ f : Fin s → A, ∀ i ∈ K, ∃ j, f j ∈ C i := by
  have hl : (0 : ℝ)<Fintype.card A := Nat.cast_pos.mpr hA
  apply exists_hit K C s
  have hpow : (0 : ℝ)<(Fintype.card A : ℝ)^s := pow_pos hl s
  have hc (i : I) (hi : i ∈ K) :
      ((Fintype.card A-(C i).card : ℕ) : ℝ)^s ≤
        (Fintype.card A : ℝ)^s*Real.exp (-(s : ℝ)*q) := by
    have hcard : (C i).card ≤ Fintype.card A := Finset.card_le_univ _
    have he : ((Fintype.card A-(C i).card : ℕ) : ℝ)/(Fintype.card A : ℝ) ≤ Real.exp (-q) := by
      rw [Nat.cast_sub hcard,sub_div,div_self hl.ne']
      exact (sub_le_sub_left (hC i hi) 1).trans (Real.one_sub_le_exp_neg q)
    have he' := pow_le_pow_left₀ (div_nonneg (Nat.cast_nonneg _) hl.le) he s
    rw [div_pow,← Real.exp_nat_mul] at he'
    have hid : (s : ℝ)*(-q)= -(s : ℝ)*q := by ring
    rw [hid] at he'
    exact (div_le_iff₀ hpow).mp he' |>.trans_eq (mul_comm _ _)
  have hh : (∑ i ∈ K, (((Fintype.card A-(C i).card : ℕ)^s : ℕ) : ℝ)) <
      (Fintype.card A : ℝ)^s := by
    calc
      _ ≤ ∑ _i ∈ K, (Fintype.card A : ℝ)^s*Real.exp (-(s : ℝ)*q) := by
        apply Finset.sum_le_sum
        intro i hi
        simpa only [Nat.cast_pow] using hc i hi
      _ = (Fintype.card A : ℝ)^s*((K.card : ℝ)*Real.exp (-(s : ℝ)*q)) := by
        simp only [Finset.sum_const,nsmul_eq_mul]
        ring
      _ < _ := by simpa using mul_lt_mul_of_pos_left hprob hpow
  exact_mod_cast hh

noncomputable def sampleSize (R : ℝ) (N : ℕ) : ℕ :=
  Nat.ceil (R*Real.log (10*((N : ℝ)+1)))

lemma sampleSize_error {R : ℝ} (hR : 0<R) (N : ℕ) :
    (N : ℝ)*Real.exp (-(sampleSize R N : ℝ)/R)<1/10 := by
  have hN : (0 : ℝ)<10*((N : ℝ)+1) := by positivity
  have hs : R*Real.log (10*((N : ℝ)+1)) ≤ (sampleSize R N : ℝ) := Nat.le_ceil _
  have hd : Real.log (10*((N : ℝ)+1)) ≤ (sampleSize R N : ℝ)/R := by
    apply (le_div_iff₀ hR).mpr
    simpa only [mul_comm] using hs
  have he : Real.exp (-(sampleSize R N : ℝ)/R) ≤ (10*((N : ℝ)+1))⁻¹ := by
    calc
      _ ≤ Real.exp (-Real.log (10*((N : ℝ)+1))) := by
        apply Real.exp_le_exp.mpr
        rw [neg_div]
        exact neg_le_neg hd
      _ = _ := by rw [Real.exp_neg,Real.exp_log hN]
  apply (mul_le_mul_of_nonneg_left he (Nat.cast_nonneg N)).trans_lt
  rw [← div_eq_mul_inv]
  apply (div_lt_iff₀ hN).mpr
  linarith

lemma sampleSize_pos {R : ℝ} (hR : 0<R) (N : ℕ) : 0<sampleSize R N := by
  apply (Nat.lt_ceil (α := ℝ)).mpr
  have hN : (1 : ℝ)<10*((N : ℝ)+1) := by have hh : (0 : ℝ) ≤ N := Nat.cast_nonneg N; linarith
  simpa using mul_pos hR (Real.log_pos hN)

lemma sampleSize_le {R : ℝ} (hR : 0<R) {N M : ℕ} (hNM : N≤M) :
    (sampleSize R N : ℝ) ≤ R*Real.log (10*((M : ℝ)+1))+1 := by
  apply le_of_lt
  have hN : (1 : ℝ) ≤ 10*((N : ℝ)+1) := by have hh : (0 : ℝ) ≤ N := Nat.cast_nonneg N; linarith
  apply (Nat.ceil_lt_add_one (mul_nonneg hR.le (Real.log_nonneg hN))).trans_le
  apply add_le_add_left
  apply mul_le_mul_of_nonneg_left _ hR.le
  exact Real.log_le_log (by positivity) (by exact_mod_cast (Nat.mul_le_mul_left 10 (Nat.add_le_add_right hNM 1)))

lemma exists_hit_large_conflicts {A I : Type*} [Fintype A]
    (hA : 0<Fintype.card A) (K : Finset I) (C : I → Finset A)
    {R : ℝ} (hR : 0<R) :
    ∃ f : Fin (sampleSize R K.card) → A,
      ∀ i ∈ K, (Fintype.card A : ℝ)/R < (C i).card → ∃ j, f j ∈ C i := by
  let B := K.filter (fun i => (Fintype.card A : ℝ)/R < (C i).card)
  have hq (i : I) (hi : i ∈ B) : 1/R ≤ ((C i).card : ℝ)/Fintype.card A := by
    have hl : (0 : ℝ)<Fintype.card A := Nat.cast_pos.mpr hA
    have hh := (Finset.mem_filter.mp hi).2
    apply le_of_lt
    apply (div_lt_div_iff₀ hR hl).mpr
    have hh' := (div_lt_iff₀ hR).mp hh
    simpa only [one_mul] using hh'
  have he : (B.card : ℝ)*Real.exp (-(sampleSize R K.card : ℝ)*(1/R))<1 := by
    apply (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Finset.card_filter_le _ _))
      (Real.exp_pos _).le).trans_lt
    have hh := sampleSize_error hR K.card
    rw [mul_one_div] at ⊢
    exact hh.trans (by norm_num)
  obtain ⟨f,hf⟩ := exists_hit_of_exponential hA B C (sampleSize R K.card) hq he
  exact ⟨f,fun i hi hci => hf i (Finset.mem_filter.mpr ⟨hi,hci⟩)⟩

lemma sum_sample_coordinate {A J : Type*} [Fintype A] [Fintype J] [DecidableEq J]
    (hA : 0<Fintype.card A) (w : A → ℝ) (j : J) :
    ∑ f : J → A, w (f j) = (Fintype.card (J → A) : ℝ)*((∑ a, w a)/Fintype.card A) := by
  let e := Equiv.piSplitAt j (fun _ : J => A)
  have he : ∑ f : J → A, w (f j) = ∑ z : A × ({i : J // i≠j} → A), w z.1 :=
    Fintype.sum_equiv e _ _ (fun _ => rfl)
  rw [he,Fintype.sum_prod_type]
  simp only [Finset.sum_const,nsmul_eq_mul,← Finset.mul_sum]
  have hc := Fintype.card_congr e
  rw [Fintype.card_prod] at hc
  have hc' : (Fintype.card (J → A) : ℝ) =
      (Fintype.card A : ℝ)*(Fintype.card ({i : J // i≠j} → A) : ℝ) := by exact_mod_cast hc
  rw [hc']
  have ha : (Fintype.card A : ℝ)≠0 := ne_of_gt (Nat.cast_pos.mpr hA)
  field_simp
  simp [mul_comm]

lemma sum_sample_cost {A : Type*} [Fintype A] (hA : 0<Fintype.card A)
    (w : A → ℝ) (s : ℕ) :
    ∑ f : Fin s → A, ∑ j, w (f j) =
      (Fintype.card A : ℝ)^s*((s : ℝ)*((∑ a, w a)/Fintype.card A)) := by
  calc
    _ = ∑ j : Fin s, ∑ f : Fin s → A, w (f j) := by exact Finset.sum_comm
    _ = ∑ _j : Fin s, (Fintype.card (Fin s → A) : ℝ)*((∑ a, w a)/Fintype.card A) := by
      apply Finset.sum_congr rfl
      intro j _
      exact sum_sample_coordinate hA w j
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Fintype.card_fun,Nat.cast_pow]
      ring

lemma exists_low_cost_in_large_set {B : Type*} [Fintype B]
    (hB : 0<Fintype.card B) (S : Finset B) (w : B → ℝ) (a : ℝ)
    (hw : ∀ b, 0≤w b) (hs : (Fintype.card B : ℝ)/2 < S.card)
    (hmean : ∑ b, w b ≤ (Fintype.card B : ℝ)*a) :
    ∃ b ∈ S, w b≤2*a := by
  have hn : S.Nonempty := Finset.card_pos.mp (by
    have hh : (0 : ℝ)<S.card := (half_pos (Nat.cast_pos.mpr hB)).trans hs
    exact_mod_cast hh)
  have ha : 0≤a := by
    have hh := (Finset.sum_nonneg (fun b _ => hw b)).trans hmean
    exact nonneg_of_mul_nonneg_right hh (Nat.cast_pos.mpr hB)
  by_contra! hbad
  have hlt : (S.card : ℝ)*(2*a) < ∑ b ∈ S, w b := by
    simpa only [Finset.sum_const,nsmul_eq_mul] using
      (Finset.sum_lt_sum_of_nonempty hn (fun b hb => hbad b hb))
  have hsum : ∑ b ∈ S, w b ≤ ∑ b, w b :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (fun b _ _ => hw b)
  have hc : (Fintype.card B : ℝ)*a ≤ (S.card : ℝ)*(2*a) := by nlinarith
  exact (not_lt_of_ge (hmean.trans hc)) (hlt.trans_le hsum)

lemma avoiding_count_le {A : Type*} [Fintype A] (hA : 0<Fintype.card A)
    (C : Finset A) (s : ℕ) {q : ℝ} (hC : q ≤ (C.card : ℝ)/Fintype.card A) :
    ((((univ : Finset (Fin s → A)).filter (fun f => ∀ j, f j ∉ C)).card) : ℝ) ≤
      (Fintype.card A : ℝ)^s*Real.exp (-(s : ℝ)*q) := by
  rw [avoiding_count,Nat.cast_pow]
  have hl : (0 : ℝ)<Fintype.card A := Nat.cast_pos.mpr hA
  have hcard : C.card ≤ Fintype.card A := Finset.card_le_univ _
  have he : ((Fintype.card A-C.card : ℕ) : ℝ)/(Fintype.card A : ℝ) ≤ Real.exp (-q) := by
    rw [Nat.cast_sub hcard,sub_div,div_self hl.ne']
    exact (sub_le_sub_left hC 1).trans (Real.one_sub_le_exp_neg q)
  have he' := pow_le_pow_left₀ (div_nonneg (Nat.cast_nonneg _) hl.le) he s
  rw [div_pow,← Real.exp_nat_mul] at he'
  have hid : (s : ℝ)*(-q)= -(s : ℝ)*q := by ring
  rw [hid] at he'
  exact (div_le_iff₀ (pow_pos hl s)).mp he' |>.trans_eq (mul_comm _ _)

lemma exists_hit_large_conflicts_with_cost {A I : Type*} [Fintype A]
    (hA : 0<Fintype.card A) (K : Finset I) (C : I → Finset A)
    (w : A → ℝ) (hw : ∀ a, 0≤w a) {R : ℝ} (hR : 0<R) :
    ∃ f : Fin (sampleSize R K.card) → A,
      (∀ i ∈ K, (Fintype.card A : ℝ)/R < (C i).card → ∃ j, f j ∈ C i) ∧
      ∑ j, w (f j) ≤ 2*(sampleSize R K.card : ℝ)*((∑ a, w a)/Fintype.card A) := by
  let s := sampleSize R K.card
  let B := K.filter (fun i => (Fintype.card A : ℝ)/R < (C i).card)
  let bad : Finset (Fin s → A) := B.biUnion
    (fun i => univ.filter (fun f => ∀ j, f j ∉ C i))
  have hl : (0 : ℝ)<Fintype.card A := Nat.cast_pos.mpr hA
  have hprob : (bad.card : ℝ) < (Fintype.card A : ℝ)^s/10 := by
    have hc (i : I) (hi : i ∈ B) :
        ((((univ : Finset (Fin s → A)).filter (fun f => ∀ j, f j ∉ C i)).card) : ℝ) ≤
          (Fintype.card A : ℝ)^s*Real.exp (-(s : ℝ)/R) := by
      have hq : 1/R ≤ ((C i).card : ℝ)/Fintype.card A := by
        apply le_of_lt
        apply (div_lt_div_iff₀ hR hl).mpr
        simpa only [one_mul] using (div_lt_iff₀ hR).mp (Finset.mem_filter.mp hi).2
      simpa only [mul_one_div] using avoiding_count_le hA (C i) s hq
    calc
      _ ≤ ∑ i ∈ B, ((((univ : Finset (Fin s → A)).filter (fun f => ∀ j, f j ∉ C i)).card) : ℝ) := by
        exact_mod_cast (Finset.card_biUnion_le (s := B) (t := fun i => (univ : Finset (Fin s → A)).filter (fun f => ∀ j, f j ∉ C i)))
      _ ≤ ∑ _i ∈ B, (Fintype.card A : ℝ)^s*Real.exp (-(s : ℝ)/R) := Finset.sum_le_sum hc
      _ = (Fintype.card A : ℝ)^s*((B.card : ℝ)*Real.exp (-(s : ℝ)/R)) := by
        simp only [Finset.sum_const,nsmul_eq_mul]; ring
      _ ≤ (Fintype.card A : ℝ)^s*((K.card : ℝ)*Real.exp (-(s : ℝ)/R)) := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg hl.le s)
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        exact_mod_cast Finset.card_filter_le K _
      _ < _ := by
        have hh := mul_lt_mul_of_pos_left (sampleSize_error hR K.card) (pow_pos hl s)
        simpa only [mul_one_div] using hh
  have htotal : Fintype.card (Fin s → A)=(Fintype.card A)^s := by simp
  have hS : (Fintype.card (Fin s → A) : ℝ)/2 < ((univ \ bad).card : ℝ) := by
    have hc := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ bad)
    have hc' : ((univ \ bad).card : ℝ)+(bad.card : ℝ)=(Fintype.card A : ℝ)^s := by
      have hh : (univ \ bad).card+bad.card=(Fintype.card A)^s := by simpa using hc
      exact_mod_cast hh
    rw [htotal,Nat.cast_pow]
    linarith [pow_pos hl s]
  obtain ⟨f,hf,hcost⟩ := exists_low_cost_in_large_set
    (by rw [htotal]; exact pow_pos hA s) (univ \ bad) (fun f => ∑ j, w (f j))
    ((s : ℝ)*((∑ a, w a)/Fintype.card A))
    (fun f => Finset.sum_nonneg (fun j _ => hw (f j))) hS
    (by rw [sum_sample_cost hA w,htotal,Nat.cast_pow])
  refine ⟨f,?_,by simpa only [mul_assoc] using hcost⟩
  intro i hi hci
  by_contra! hn
  exact (Finset.mem_sdiff.mp hf).2 (Finset.mem_biUnion.mpr
    ⟨i,Finset.mem_filter.mpr ⟨hi,hci⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩⟩)

end PlanarUnitDistances.FiniteSampling

namespace PlanarUnitDistances.CircleCutting
open Finset Classical

noncomputable def conflicts (Q : Finset Plane) (U : Set Plane) : Finset Plane :=
  Q.filter (fun c => ∃ p ∈ U, dist p c=1)

lemma conflicts_subtype_card (Q : Finset Plane) (U : Set Plane) :
    ((univ : Finset Q).filter (fun (c : Q) => ∃ p ∈ U, dist p (c : Plane)=1)).card=(conflicts Q U).card := by
  apply Finset.card_bij (fun (c : Q) _ => (c : Plane))
  · intro c hc
    exact Finset.mem_filter.mpr ⟨c.property,(Finset.mem_filter.mp hc).2⟩
  · intro c _ d _ h
    exact Subtype.ext h
  · intro c hc
    exact ⟨⟨c,(Finset.mem_filter.mp hc).1⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hc).2⟩,rfl⟩

theorem cutting_good_position (P Q : Finset Plane) (hQ : Q.Nonempty)
    (hpos : ∀ T ⊆ Q, ∀ p ∈ P, (∀ c ∈ T, dist p c≠1) → p 0 ∉ eventAbscissas T)
    (w : Plane → ℝ) (hw : ∀ c ∈ Q, 0≤w c) {R : ℝ} (hR : 0<R) :
    ∃ (f : Fin (FiniteSampling.sampleSize R (candidateCodes Q).card) → Plane)
      (D : Finset (Set Plane)),
      (∀ j, f j ∈ Q) ∧
      (∑ j, w (f j) ≤ 2*(FiniteSampling.sampleSize R (candidateCodes Q).card : ℝ)*
        ((∑ c ∈ Q, w c)/Q.card)) ∧
      D.card ≤ 43*(1+(FiniteSampling.sampleSize R (candidateCodes Q).card)^2) ∧
      (∀ U ∈ D, IsOpen U ∧ ((conflicts Q U).card : ℝ)≤(Q.card : ℝ)/R) ∧
      (∀ p ∈ P, (∀ j, dist p (f j)≠1) → ∃ U ∈ D, p ∈ U) := by
  let C (r : RegionCode) : Finset Q := univ.filter (fun (c : Q) => ∃ p ∈ codeRegion r, dist p (c : Plane)=1)
  have hl : 0<Fintype.card Q := by simpa using hQ.card_pos
  obtain ⟨f,hf,hcost⟩ := FiniteSampling.exists_hit_large_conflicts_with_cost hl (candidateCodes Q)
    C (fun c => w c) (fun c => hw c c.property) hR
  let T := univ.image (fun j => (f j : Plane))
  have hT : T ⊆ Q := by
    intro c hc
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hc
    exact (f j).property
  obtain ⟨d⟩ := arrangement_exists T
  let D := d.pieces.image (fun r => region d.a r.1 r.2.1 r.2.2)
  refine ⟨fun j => f j,D,fun j => (f j).property,?_,?_,?_,?_⟩
  · have hs : ∑ c ∈ Q, w c=∑ c : Q, w c := Finset.sum_subtype Q (fun _ => Iff.rfl) w
    simpa only [hs,Fintype.card_coe] using hcost
  · apply Finset.card_image_le.trans (d.pieces_card.trans ?_)
    have ht : T.card ≤ FiniteSampling.sampleSize R (candidateCodes Q).card := by
      exact Finset.card_image_le.trans_eq (by simp)
    gcongr
  · intro U hU
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hU
    refine ⟨region_open _ _ _ _,?_⟩
    obtain ⟨c,hc,he⟩ := d.piece_description hT hr
    by_contra! hbad
    have hbig : (Fintype.card Q : ℝ)/R < ((C c).card : ℝ) := by
      simpa only [C,conflicts_subtype_card,Fintype.card_coe,← he] using hbad
    obtain ⟨j,hj⟩ := hf c hc hbig
    obtain ⟨p,hp,hpf⟩ := (Finset.mem_filter.mp hj).2
    rw [← he] at hp
    exact d.piece_avoids hr p hp (f j) (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩) hpf
  · intro p hp havoid
    have hpT : ∀ c ∈ T, dist p c≠1 := by
      intro c hc
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hc
      exact havoid j
    obtain ⟨r,hr,hpr⟩ := d.pieces_cover (hpos T hT p hp hpT) hpT
    exact ⟨_,Finset.mem_image.mpr ⟨r,hr,rfl⟩,hpr⟩

lemma rotate_continuous (e : Plane) : Continuous (rotate e) := by
  unfold rotate projection
  fun_prop

lemma conflicts_rotate (Q : Finset Plane) (e : Plane) (he : (e 0)^2+(e 1)^2=1)
    (U : Set Plane) :
    conflicts (Q.image (rotate e)) U=(conflicts Q ((rotate e) ⁻¹' U)).image (rotate e) := by
  ext c
  simp only [conflicts,Finset.mem_filter,Finset.mem_image]
  constructor
  · rintro ⟨⟨c,hc,rfl⟩,p,hp,hpc⟩
    obtain ⟨p,rfl⟩ := rotate_surjective e he p
    exact ⟨c,⟨hc,p,hp,by simpa only [rotate_dist e he] using hpc⟩,rfl⟩
  · rintro ⟨c,⟨hc,p,hp,hpc⟩,rfl⟩
    exact ⟨⟨c,hc,rfl⟩,rotate e p,hp,by simpa only [rotate_dist e he] using hpc⟩

noncomputable def cuttingLog (l : ℕ) : ℝ := Real.log (10*(81*(1+(l : ℝ))^6+1))

theorem cutting_with_cost (P Q : Finset Plane) (hQ : Q.Nonempty)
    (w : Plane → ℝ) (hw : ∀ c ∈ Q, 0≤w c) {R : ℝ} (hR : 0<R) :
    ∃ (s : ℕ) (T : Finset Plane) (D : Finset (Set Plane)),
      (s : ℝ) ≤ R*cuttingLog Q.card+1 ∧ T ⊆ Q ∧ T.card ≤ s ∧
      (∑ c ∈ T, w c ≤ 2*(s : ℝ)*((∑ c ∈ Q, w c)/Q.card)) ∧
      D.card ≤ 43*(1+s^2) ∧
      (∀ U ∈ D, IsOpen U ∧ ((conflicts Q U).card : ℝ)≤(Q.card : ℝ)/R) ∧
      (∀ p ∈ P, (∀ c ∈ T, dist p c≠1) → ∃ U ∈ D, p ∈ U) := by
  obtain ⟨e,he,hpos⟩ := good_rotated_position P Q
  let v : Plane ≃ Plane := Equiv.ofBijective (rotate e) ⟨rotate_injective e he,rotate_surjective e he⟩
  have hv (p : Plane) : v p=rotate e p := rfl
  let Q' := Q.image (rotate e)
  obtain ⟨f,D,hf,hcost,hD,hconf,hcover⟩ := cutting_good_position
    (P.image (rotate e)) Q' (Finset.Nonempty.image hQ _) hpos (fun c => w (v.symm c))
    (by intro c hc; change c ∈ Q.image (rotate e) at hc
        obtain ⟨c₀,hc₀,heq⟩ := Finset.mem_image.mp hc
        rw [← heq,← hv,Equiv.symm_apply_apply]
        exact hw c₀ hc₀) hR
  let s := FiniteSampling.sampleSize R (candidateCodes Q').card
  let g : Fin s → Plane := fun j => v.symm (f j)
  let T := univ.image g
  let D' := D.image (fun U => (rotate e) ⁻¹' U)
  have hcQ : Q'.card=Q.card := Finset.card_image_of_injective Q (rotate_injective e he)
  have hsum : ∑ c ∈ Q', (fun c => w (v.symm c)) c=∑ c ∈ Q, w c := by
    rw [Finset.sum_image (rotate_injective e he).injOn]
    simp only [← hv,Equiv.symm_apply_apply]
  have hg (j : Fin s) : g j ∈ Q := by
    obtain ⟨c,hc,hcf⟩ := Finset.mem_image.mp (hf j)
    have hh : g j=c := by change v.symm (f j)=c; rw [← hcf,← hv,v.symm_apply_apply]
    rwa [hh]
  refine ⟨s,T,D',?_,?_,?_,?_,?_,?_,?_⟩
  · have hh := FiniteSampling.sampleSize_le hR (candidateCodes_card Q')
    simpa only [hcQ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_pow,cuttingLog,Nat.cast_ofNat] using hh
  · intro c hc
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hc
    exact hg j
  · exact Finset.card_image_le.trans_eq (by simp)
  · have hh : ∑ c ∈ T, w c ≤ ∑ j, w (g j) :=
      Finset.sum_image_le_of_nonneg (fun c hc => by
        obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hc
        exact hw _ (hg j))
    exact hh.trans (by simpa only [hsum,hcQ,Function.comp_apply] using hcost)
  · exact Finset.card_image_le.trans hD
  · intro U hU
    obtain ⟨V,hV,rfl⟩ := Finset.mem_image.mp hU
    refine ⟨(hconf V hV).1.preimage (rotate_continuous e),?_⟩
    have hh := (hconf V hV).2
    rw [conflicts_rotate Q e he,Finset.card_image_of_injective _ (rotate_injective e he),hcQ] at hh
    exact hh
  · intro p hp havoid
    have ha : ∀ j, dist (rotate e p) (f j)≠1 := by
      intro j hj
      have hh : f j=rotate e (g j) := (v.apply_symm_apply (f j)).symm
      rw [hh,rotate_dist e he] at hj
      exact havoid (g j) (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩) hj
    obtain ⟨U,hU,hpU⟩ := hcover (rotate e p) (Finset.mem_image.mpr ⟨p,hp,rfl⟩) ha
    exact ⟨_,Finset.mem_image.mpr ⟨U,hU,rfl⟩,hpU⟩

end PlanarUnitDistances.CircleCutting

namespace PlanarUnitDistances.CircleIncidence
open Real

lemma cutting_small_parameter {m l R : ℝ} (hm : 0 ≤ m) (hl : 0 ≤ l)
    (hR : 0 ≤ R) (hR1 : R ≤ 1) (he : R^3*l=m^2) : m*sqrt l ≤ l := by
  have hR3 : R^3 ≤ 1 := by simpa using pow_le_one₀ hR hR1 (n := 3)
  have hsq : m^2 ≤ l := by nlinarith
  have hp := mul_le_mul_of_nonneg_right hsq hl
  have hs := Real.sq_sqrt hl
  have he' : (m*sqrt l)^2=m^2*l := by rw [mul_pow,hs]
  have hmn : 0 ≤ m*sqrt l := mul_nonneg hm (sqrt_nonneg l)
  nlinarith

lemma cutting_large_parameter {m l R L : ℝ} (hm : 0 ≤ m) (hl : 0 < l)
    (hml : m ≤ l) (_hR : 0 ≤ R) (hL : 1 ≤ L) (he : R^3*l=m^2)
    (hlarge : l < 4*(R*L+1)) : l ≤ 32*L^2 := by
  have hLn : 0 ≤ L := by linarith
  have hL2 : 1 ≤ L^2 := by nlinarith
  by_cases hl8 : l ≤ 8
  · nlinarith
  have hlarge' : l ≤ 8*R*L := by linarith
  have hR3 : R^3 ≤ l := by
    have hs : m^2 ≤ l^2 := (sq_le_sq₀ hm hl.le).mpr hml
    nlinarith
  have hc := pow_le_pow_left₀ hl.le hlarge' 3
  have hc' : l^3 ≤ 512*l*L^3 := by
    have hh := mul_le_mul_of_nonneg_right hR3 (show 0 ≤ 512*L^3 by positivity)
    nlinarith only [hc,hh]
  have hc'' : l^2 ≤ 512*L^3 := by nlinarith only [hc',hl]
  have hLpow : L^3 ≤ L^4 := by
    exact pow_le_pow_right₀ hL (by norm_num)
  have hh : l^2 ≤ (32*L^2)^2 := by nlinarith only [hc'',hLpow,sq_nonneg (L^2)]
  exact (sq_le_sq₀ hl.le (by positivity)).mp hh

lemma cutting_sqrt_identity {m l R : ℝ} (hm : 0 ≤ m) (hl : 0 ≤ l) (hR : 0 < R)
    (he : R^3*l=m^2) : m*sqrt (l/R)=R*l := by
  have hs := Real.sq_sqrt (div_nonneg hl hR.le)
  have heq : (m*sqrt (l/R))^2=(R*l)^2 := by
    rw [mul_pow,hs,← he]
    field_simp
  exact (sq_eq_sq₀ (by positivity) (by positivity)).mp heq

lemma cutting_absorbed_numeric {m l R L : ℝ} (hm : 0 ≤ m) (hl : 0 ≤ l)
    (hR : 1 ≤ R) (hL : 1 ≤ L) (he : R^3*l=m^2) :
    4*(R*L+1)*l+4*m*sqrt (l/R)+172*(1+(R*L+1)^2)*(l/R) ≤
      1000*L^2*(R*l+m+l) := by
  have hRp : 0 < R := by linarith
  have hLn : 0 ≤ L := by linarith
  have hR2 : 1 ≤ R*L := by nlinarith
  have hL2 : L ≤ L^2 := by nlinarith
  have hRLn : 0 ≤ R*L := by positivity
  have ha : R*L+1 ≤ 2*(R*L) := by linarith
  have hb := (sq_le_sq₀ (show 0 ≤ R*L+1 by positivity) (show 0 ≤ 2*(R*L) by positivity)).mpr ha
  have hc : 1+(R*L+1)^2 ≤ 5*R^2*L^2 := by nlinarith [sq_nonneg (R*L-1)]
  have hd := mul_le_mul_of_nonneg_right hc (div_nonneg hl hRp.le)
  have hd' : (5*R^2*L^2)*(l/R)=5*R*L^2*l := by field_simp
  rw [hd'] at hd
  have ha' := mul_le_mul_of_nonneg_right ha hl
  have hLL := mul_le_mul_of_nonneg_left hL2 (show 0 ≤ R*l by positivity)
  have hsq := cutting_sqrt_identity hm hl hRp he
  have hlo : R*l ≤ R*L^2*l := by
    have hLsq : 1 ≤ L^2 := by nlinarith
    have hh := mul_le_mul_of_nonneg_left hLsq (show 0 ≤ R*l by positivity)
    nlinarith
  have hmn : 0 ≤ L^2*m := by positivity
  have hln : 0 ≤ L^2*l := by positivity
  nlinarith only [hd,ha',hLL,hsq,hlo,hmn,hln]

lemma cutting_parameter_exists {m l : ℝ} (hm : 0 < m) (hl : 0 < l) :
    ∃ R : ℝ, 0 < R ∧ R^3*l=m^2 ∧ R*l=(m*l)^((2:ℝ)/3) := by
  let R : ℝ := (m^2/l)^((1:ℝ)/3)
  have hb : 0 < m^2/l := div_pos (sq_pos_of_pos hm) hl
  have hR : 0 < R := Real.rpow_pos_of_pos hb _
  have he : R^3*l=m^2 := by
    have hh : R^3=m^2/l := by
      change ((m^2/l)^((1:ℝ)/3))^3=m^2/l
      rw [← Real.rpow_mul_natCast hb.le]
      norm_num
    rw [hh,div_mul_cancel₀ _ hl.ne']
  refine ⟨R,hR,he,?_⟩
  have hn := Real.rpow_nonneg (mul_pos hm hl).le ((2:ℝ)/3)
  have hs : ((m*l)^((2:ℝ)/3))^3=(m*l)^2 := by
    rw [← Real.rpow_mul_natCast (mul_pos hm hl).le]
    norm_num
  have hh : (R*l)^3=((m*l)^((2:ℝ)/3))^3 := by
    rw [hs]
    calc
      (R*l)^3 = (R^3*l)*l^2 := by ring
      _ = m^2*l^2 := by rw [he]
      _ = (m*l)^2 := by ring
  exact (pow_left_inj₀ (mul_pos hR hl).le hn (by norm_num : 3≠0)).mp hh

end PlanarUnitDistances.CircleIncidence

namespace PlanarUnitDistances.CircleIncidence
open Finset Classical
open CircleCutting

noncomputable def degree (P : Finset Plane) (q : Plane) : ℝ :=
  ((P.filter (fun p => dist p q=1)).card : ℝ)

noncomputable def incidences (P Q : Finset Plane) : ℝ := ∑ q ∈ Q, degree P q

lemma degree_sum (P : Finset Plane) (q : Plane) :
    degree P q = ∑ p ∈ P, if dist p q=1 then (1 : ℝ) else 0 := by
  simp [degree,Finset.sum_boole]

lemma degree_nonneg (P : Finset Plane) (q : Plane) : 0 ≤ degree P q := Nat.cast_nonneg _

lemma incidences_nonneg (P Q : Finset Plane) : 0  ≤  incidences P Q :=
  Finset.sum_nonneg (fun q _ => degree_nonneg P q)

lemma incidences_comm (P Q : Finset Plane) : incidences P Q=incidences Q P := by
  unfold incidences
  simp_rw [degree_sum]
  rw [Finset.sum_comm]
  simp only [dist_comm]

lemma degree_le (P : Finset Plane) (q : Plane) : degree P q ≤ P.card :=
  Nat.cast_le.mpr (Finset.card_filter_le _ _)

lemma incidences_le (P Q : Finset Plane) : incidences P Q ≤ (P.card : ℝ)*Q.card := by
  apply (Finset.sum_le_sum (fun q _ => degree_le P q)).trans_eq
  simp [mul_comm]

noncomputable def common (Q : Finset Plane) (p r : Plane) : ℝ :=
  ((Q.filter (fun q => dist p q=1 ∧ dist r q=1)).card : ℝ)

lemma common_sum (Q : Finset Plane) (p r : Plane) :
    common Q p r = ∑ q ∈ Q, (if dist p q=1 then (1 : ℝ) else 0)*(if dist r q=1 then 1 else 0) := by
  simp only [common,← Finset.sum_boole]
  apply Finset.sum_congr rfl
  intro q _
  split_ifs <;> simp_all

lemma common_le_two (Q : Finset Plane) (p r : Plane) (hpr : p≠r) : common Q p r ≤ 2 := by
  apply Nat.cast_le.mpr
  apply circle_intersection_card p r hpr
  intro q hq
  simpa only [dist_comm] using (Finset.mem_filter.mp hq).2

lemma common_self (Q : Finset Plane) (p : Plane) : common Q p p=degree Q p := by
  simp only [common,degree,and_self,dist_comm]

lemma degree_sq_sum (P Q : Finset Plane) :
    ∑ q ∈ Q, (degree P q)^2 = ∑ p ∈ P, ∑ r ∈ P, common Q p r := by
  simp_rw [degree_sum,pow_two,Finset.sum_mul,Finset.mul_sum,common_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_comm]

lemma degree_sq_bound (P Q : Finset Plane) :
    ∑ q ∈ Q, (degree P q)^2  ≤  incidences P Q+2*(P.card : ℝ)^2 := by
  rw [degree_sq_sum]
  have h (p : Plane) (hp : p ∈ P) : ∑ r ∈ P, common Q p r  ≤  degree Q p+2*(P.card : ℝ) := by
    rw [← Finset.sum_erase_add _ _ hp,common_self]
    have hh : ∑ r ∈ P.erase p, common Q p r  ≤  2*(P.card : ℝ) := by
      apply (Finset.sum_le_sum (fun r hr => common_le_two Q p r (Finset.ne_of_mem_erase hr).symm)).trans
      simp only [Finset.sum_const,nsmul_eq_mul]
      have hc : ((P.erase p).card : ℝ) ≤ (P.card : ℝ) := Nat.cast_le.mpr (Finset.card_erase_le)
      linarith
    linarith
  apply (Finset.sum_le_sum h).trans_eq
  rw [Finset.sum_add_distrib]
  change incidences Q P + _ = _
  rw [incidences_comm Q P]
  simp only [Finset.sum_const,nsmul_eq_mul]
  ring

lemma incidences_pair_bound (P Q : Finset Plane) :
    incidences P Q  ≤  2*(P.card : ℝ)*Real.sqrt (Q.card : ℝ)+2*Q.card := by
  have hcs : (incidences P Q)^2  ≤  (Q.card : ℝ)*(∑ q ∈ Q, (degree P q)^2) := sq_sum_le_card_mul_sum_sq
  have hsq := degree_sq_bound P Q
  have hn := incidences_nonneg P Q
  have hm : (0 : ℝ) ≤ P.card := Nat.cast_nonneg _
  have hl : (0 : ℝ) ≤ Q.card := Nat.cast_nonneg _
  have hr := Real.sqrt_nonneg (Q.card : ℝ)
  have he := Real.sq_sqrt hl
  have hh : (incidences P Q)^2  ≤  (Q.card : ℝ)*(incidences P Q+2*(P.card : ℝ)^2) :=
    hcs.trans (mul_le_mul_of_nonneg_left hsq hl)
  by_contra! hbad
  have ht : 0 ≤ 2*(P.card : ℝ)*Real.sqrt (Q.card : ℝ)+2*Q.card := by positivity
  have hmul : (2*(P.card : ℝ)*Real.sqrt (Q.card : ℝ)+2*Q.card)^2 < (incidences P Q)^2 := by nlinarith
  have hh' : (incidences P Q-2*(Q.card : ℝ))^2 ≤ 2*(P.card : ℝ)^2*(Q.card : ℝ) := by
    have hi : (2 : ℝ)*Q.card < incidences P Q := by nlinarith
    nlinarith
  have hz : 0 ≤ 2*(P.card : ℝ)*Real.sqrt (Q.card : ℝ) := by positivity
  have hi : 2*(P.card : ℝ)*Real.sqrt (Q.card : ℝ) < incidences P Q-2*(Q.card : ℝ) := by linarith
  have hs := (sq_lt_sq₀ hz (hz.trans hi.le)).mpr hi
  have hid : ((P.card : ℝ)*Real.sqrt (Q.card : ℝ))^2=(P.card : ℝ)^2*(Q.card : ℝ) := by rw [mul_pow,he]
  nlinarith [sq_nonneg ((P.card : ℝ)*Real.sqrt (Q.card : ℝ))]

lemma degree_mono {P P' : Finset Plane} (h : P ⊆ P') (q : Plane) : degree P q ≤ degree P' q := by
  apply Nat.cast_le.mpr
  exact Finset.card_le_card (Finset.filter_subset_filter _ h)

lemma incidences_mono_left {P P' : Finset Plane} (h : P ⊆ P') (Q : Finset Plane) :
    incidences P Q  ≤  incidences P' Q :=
  Finset.sum_le_sum (fun q _ => degree_mono h q)

lemma incidences_mono_right (P : Finset Plane) {Q Q' : Finset Plane} (h : Q ⊆ Q') :
    incidences P Q  ≤  incidences P Q' :=
  Finset.sum_le_sum_of_subset_of_nonneg h (fun q _ _ => degree_nonneg P q)

lemma incidences_filter_split (P Q : Finset Plane) (A : Plane → Prop) :
    incidences P Q=incidences (P.filter A) Q+incidences (P.filter (fun p => ¬ A p)) Q := by
  rw [incidences_comm P Q,incidences_comm (P.filter A) Q,
    incidences_comm (P.filter (fun p => ¬ A p)) Q]
  exact (Finset.sum_filter_add_sum_filter_not P A (degree Q)).symm

noncomputable def retained (P T : Finset Plane) : Finset Plane :=
  P.filter (fun p => ∀ c ∈ T, dist p c≠1)

noncomputable def deleted (P T : Finset Plane) : Finset Plane :=
  P.filter (fun p => ∃ c ∈ T, dist p c=1)

lemma incidence_deletion_split (P Q T : Finset Plane) :
    incidences P Q=incidences (retained P T) Q+incidences (deleted P T) Q := by
  rw [incidences_filter_split P Q (fun p => ∀ c ∈ T, dist p c≠1)]
  congr 1
  · apply congrArg (fun S => incidences S Q)
    ext p
    simp only [Finset.mem_filter,retained]
  · apply congrArg (fun S => incidences S Q)
    ext p
    simp only [Finset.mem_filter,deleted,not_forall,not_not,exists_prop]

lemma deleted_degree_le (P T : Finset Plane) (q : Plane) (hq : q ∉ T) :
    degree (deleted P T) q  ≤  2*T.card := by
  let B (c : Plane) := P.filter (fun p => dist p c=1 ∧ dist p q=1)
  have hsub : (deleted P T).filter (fun p => dist p q=1) ⊆ T.biUnion B := by
    intro p hp
    obtain ⟨hp,hpq⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp,c,hc,hpc⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_biUnion.mpr ⟨c,hc,Finset.mem_filter.mpr ⟨hp,hpc,hpq⟩⟩
  have hc (c : Plane) (hmem : c ∈ T) : (B c).card ≤ 2 :=
    circle_intersection_card c q (fun he => hq (he ▸ hmem)) (B c)
      (fun p hp => (Finset.mem_filter.mp hp).2)
  have hh : ((deleted P T).filter (fun p => dist p q=1)).card  ≤  ∑ _c ∈ T, (2 : ℕ) :=
    (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans (Finset.sum_le_sum hc))
  have hsum : (∑ _c ∈ T, (2 : ℕ))=2*T.card := by simp [mul_comm]
  rw [hsum] at hh
  unfold degree
  exact_mod_cast hh

lemma deleted_incidence_le (P Q T : Finset Plane) (hT : T ⊆ Q) :
    incidences (deleted P T) Q  ≤  incidences P T+2*(T.card : ℝ)*Q.card := by
  have he : incidences (deleted P T) Q = incidences (deleted P T) T+
      incidences (deleted P T) (Q \ T) := by
    unfold incidences
    have hh := Finset.sum_sdiff (f := degree (deleted P T)) hT
    linarith
  rw [he]
  have hT' : incidences (deleted P T) T  ≤  incidences P T :=
    incidences_mono_left (Finset.filter_subset _ _) T
  have hrest : incidences (deleted P T) (Q \ T)  ≤  2*(T.card : ℝ)*Q.card := by
    apply (Finset.sum_le_sum (fun q hq => deleted_degree_le P T q (Finset.mem_sdiff.mp hq).2)).trans
    simp only [Finset.sum_const,nsmul_eq_mul]
    have hh : ((Q \ T).card : ℝ) ≤ (Q.card : ℝ) := Nat.cast_le.mpr (Finset.card_le_card Finset.sdiff_subset)
    have hn : (0 : ℝ) ≤ T.card := Nat.cast_nonneg _
    nlinarith
  exact add_le_add hT' hrest

lemma incidence_in_region (P Q : Finset Plane) (U : Set Plane) (hP : ∀ p ∈ P, p ∈ U) :
    incidences P Q=incidences P (conflicts Q U) := by
  apply (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
  intro q hq hnot
  unfold degree
  have he : P.filter (fun p => dist p q=1)=∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    obtain ⟨hp,hpq⟩ := Finset.mem_filter.mp hp
    exact hnot (Finset.mem_filter.mpr ⟨hq,p,hP p hp,hpq⟩)
  rw [he,Finset.card_empty,Nat.cast_zero]

lemma incidence_partition {P Q : Finset Plane} {D : Finset (Set Plane)} (a : Plane → Set Plane)
    (ha : ∀ p ∈ P, a p ∈ D) :
    (∑ U ∈ D, incidences (P.filter (fun p => a p=U)) Q)=incidences P Q := by
  rw [incidences_comm P Q]
  have h (U : Set Plane) : incidences (P.filter (fun p => a p=U)) Q =
      ∑ p ∈ P.filter (fun p => a p=U), degree Q p := incidences_comm _ _
  simp_rw [h]
  exact Finset.sum_fiberwise_of_maps_to ha (degree Q)

lemma incidence_cutting_regions (P Q : Finset Plane) (D : Finset (Set Plane))
    {b : ℝ} (hconf : ∀ U ∈ D, ((conflicts Q U).card : ℝ) ≤ b)
    (hcover : ∀ p ∈ P, ∃ U ∈ D, p ∈ U) :
    incidences P Q  ≤  2*(P.card : ℝ)*Real.sqrt b+2*(D.card : ℝ)*b := by
  choose a ham hamem using hcover
  let f (p : Plane) : Set Plane := if hp : p ∈ P then a p hp else ∅
  have hf (p : Plane) (hp : p ∈ P) : f p ∈ D ∧ p ∈ f p := by
    simpa only [f,dite_eq_left hp] using And.intro (ham p hp) (hamem p hp)
  let B (U : Set Plane) := P.filter (fun p => f p=U)
  have hB (U : Set Plane) : ∀ p ∈ B U, p ∈ U := by
    intro p hp
    obtain ⟨hp,hpU⟩ := Finset.mem_filter.mp hp
    exact hpU ▸ (hf p hp).2
  have hc (U : Set Plane) (hU : U ∈ D) :
      incidences (B U) Q  ≤  2*((B U).card : ℝ)*Real.sqrt b+2*b := by
    rw [incidence_in_region (B U) Q U (hB U)]
    apply (incidences_pair_bound _ _).trans
    have hs := Real.sqrt_le_sqrt (hconf U hU)
    have hn : (0 : ℝ) ≤ (B U).card := Nat.cast_nonneg _
    nlinarith [hconf U hU]
  have hsum : ∑ U ∈ D, ((B U).card : ℝ)=(P.card : ℝ) := by
    have hh := Finset.sum_fiberwise_of_maps_to (fun p hp => (hf p hp).1) (fun _ : Plane => (1 : ℝ))
    simpa only [Finset.sum_const,nsmul_eq_mul,mul_one] using hh
  rw [← incidence_partition f (fun p hp => (hf p hp).1)]
  apply (Finset.sum_le_sum hc).trans_eq
  rw [Finset.sum_add_distrib]
  rw [← Finset.sum_mul,← Finset.mul_sum,hsum]
  simp only [Finset.sum_const,nsmul_eq_mul]
  ring

theorem incidence_cutting_recurrence (P Q : Finset Plane) (hQ : Q.Nonempty)
    {R : ℝ} (hR : 0 < R) :
    ∃ s : ℕ, (s : ℝ) ≤ R*cuttingLog Q.card+1 ∧
      incidences P Q  ≤  2*(s : ℝ)*(incidences P Q/Q.card)+2*(s : ℝ)*Q.card+
        2*(P.card : ℝ)*Real.sqrt ((Q.card : ℝ)/R)+86*(1+(s : ℝ)^2)*((Q.card : ℝ)/R) := by
  obtain ⟨s,T,D,hs,hT,hTs,hcost,hD,hconf,hcover⟩ :=
    cutting_with_cost P Q hQ (degree P) (fun q _ => degree_nonneg P q) hR
  refine ⟨s,hs,?_⟩
  have hp : incidences (retained P T) Q  ≤
      2*(P.card : ℝ)*Real.sqrt ((Q.card : ℝ)/R)+86*(1+(s : ℝ)^2)*((Q.card : ℝ)/R) := by
    have hh := incidence_cutting_regions (retained P T) Q D
      (fun U hU => (hconf U hU).2)
      (fun p hp => hcover p (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp).2)
    apply hh.trans
    have hpc : ((retained P T).card : ℝ) ≤ (P.card : ℝ) :=
      Nat.cast_le.mpr (Finset.card_filter_le _ _)
    have hdc : (D.card : ℝ) ≤ 43*(1+(s : ℝ)^2) := by exact_mod_cast hD
    have hn : 0 ≤ (Q.card : ℝ)/R := div_nonneg (Nat.cast_nonneg _) hR.le
    have h1 := mul_le_mul_of_nonneg_right hpc (Real.sqrt_nonneg ((Q.card : ℝ)/R))
    have h2 := mul_le_mul_of_nonneg_right hdc hn
    linarith
  have hd := deleted_incidence_le P Q T hT
  have ht : (T.card : ℝ) ≤ s := Nat.cast_le.mpr hTs
  change incidences P T ≤ 2*(s : ℝ)*(incidences P Q/Q.card) at hcost
  have hmul := mul_le_mul_of_nonneg_right ht (Nat.cast_nonneg Q.card : (0 : ℝ) ≤ Q.card)
  have hsplit := incidence_deletion_split P Q T
  linarith

lemma incidence_cutting_absorbed (P Q : Finset Plane) (hQ : Q.Nonempty)
    {R L : ℝ} (hR : 0 < R) (hL : cuttingLog Q.card ≤ L)
    (hsmall : 4*(R*L+1) ≤ (Q.card : ℝ)) :
    incidences P Q  ≤  4*(R*L+1)*(Q.card : ℝ)+4*(P.card : ℝ)*Real.sqrt ((Q.card : ℝ)/R)+
      172*(1+(R*L+1)^2)*((Q.card : ℝ)/R) := by
  obtain ⟨s,hs,hi⟩ := incidence_cutting_recurrence P Q hQ hR
  have hs' : (s : ℝ) ≤ R*L+1 := hs.trans (by nlinarith)
  have hsn : (0 : ℝ) ≤ s := Nat.cast_nonneg _
  have hrl : 0 ≤ R*L+1 := hsn.trans hs'
  have hsq : (s : ℝ)^2 ≤ (R*L+1)^2 := sq_le_sq₀ hsn hrl |>.mpr hs'
  have hl : (0 : ℝ)<Q.card := Nat.cast_pos.mpr hQ.card_pos
  have hn := incidences_nonneg P Q
  have hcost : 2*(s : ℝ)*(incidences P Q/Q.card) ≤ incidences P Q/2 := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hl).mpr
    have hh : 4*(s : ℝ) ≤ (Q.card : ℝ) := by linarith
    have hh' := mul_le_mul_of_nonneg_right hh hn
    nlinarith
  have h1 := mul_le_mul_of_nonneg_right hs' hl.le
  have h2 := mul_le_mul_of_nonneg_right hsq (div_nonneg hl.le hR.le)
  linarith

lemma cuttingLog_one_le (l : ℕ) : 1 ≤ cuttingLog l := by
  have hn : (0 : ℝ) ≤ l := Nat.cast_nonneg _
  have hp : (1 : ℝ) ≤ (1+(l : ℝ))^6 := by
    simpa only [one_pow] using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) (by linarith : (1 : ℝ) ≤ 1+l) 6
  apply (Real.le_log_iff_exp_le (by positivity : 0 < 10*(81*(1+(l : ℝ))^6+1))).mpr
  exact Real.exp_one_lt_three.le.trans (by nlinarith)

lemma cuttingLog_mono : Monotone cuttingLog := by
  intro a b hab
  have hh : (a : ℝ) ≤ b := Nat.cast_le.mpr hab
  apply Real.log_le_log (by positivity)
  have hp := pow_le_pow_left₀ (show (0 : ℝ) ≤ 1+a by positivity) (show (1 : ℝ)+a ≤ 1+b by linarith) 6
  nlinarith only [hp]

lemma incidence_bound_oriented (P Q : Finset Plane) (hPQ : P.card ≤ Q.card)
    {L : ℝ} (hL : 1 ≤ L) (hLog : cuttingLog Q.card ≤ L) :
    incidences P Q ≤ 1000*L^2*(((P.card : ℝ)*Q.card)^((2:ℝ)/3)+P.card+Q.card) := by
  by_cases hp : P.Nonempty
  · have hm : (0 : ℝ)<P.card := Nat.cast_pos.mpr hp.card_pos
    have hml : (P.card : ℝ) ≤ Q.card := Nat.cast_le.mpr hPQ
    have hl : (0 : ℝ)<Q.card := hm.trans_le hml
    have hq : Q.Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp hl)
    obtain ⟨R,hR,he,ha⟩ := cutting_parameter_exists hm hl
    rw [← ha]
    have hLsq : 1 ≤ L^2 := by nlinarith
    have hLn : 0 ≤ L := by linarith
    have hpos : 0 ≤ L^2*(R*(Q.card : ℝ)+P.card) := by positivity
    by_cases hR1 : R ≤ 1
    · have hs := cutting_small_parameter hm.le hl.le hR.le hR1 he
      have hi := incidences_pair_bound P Q
      have hh := mul_le_mul_of_nonneg_right hLsq hl.le
      nlinarith only [hs,hi,hh,hpos]
    · have hR1' : 1 ≤ R := (le_of_not_ge hR1)
      by_cases hsmall : 4*(R*L+1) ≤ (Q.card : ℝ)
      · exact (incidence_cutting_absorbed P Q hq hR hLog hsmall).trans
          (cutting_absorbed_numeric hm.le hl.le hR1' hL he)
      · have hs := cutting_large_parameter hm.le hl hml hR.le hL he (lt_of_not_ge hsmall)
        have hp := mul_le_mul_of_nonneg_left hs hm.le
        have hi := incidences_le P Q
        have hn : 0 ≤ L^2*(R*(Q.card : ℝ)+Q.card) := by positivity
        have hn' : 0 ≤ L^2*(P.card : ℝ) := by positivity
        nlinarith only [hp,hi,hn,hn']
  · have he : P=∅ := Finset.not_nonempty_iff_eq_empty.mp hp
    subst P
    simp only [incidences,degree,Finset.filter_empty,Finset.card_empty,Nat.cast_zero,
      Finset.sum_const_zero,zero_mul,Real.zero_rpow (by norm_num : (2:ℝ)/3≠0),zero_add]
    positivity

theorem incidence_bound (P Q : Finset Plane) :
    incidences P Q ≤ 1000*(cuttingLog (P.card+Q.card))^2*
      (((P.card : ℝ)*Q.card)^((2:ℝ)/3)+P.card+Q.card) := by
  have hL := cuttingLog_one_le (P.card+Q.card)
  rcases le_total P.card Q.card with h|h
  · exact incidence_bound_oriented P Q h hL
      (cuttingLog_mono (Nat.le_add_left _ _))
  · have hh := incidence_bound_oriented Q P h hL
      (cuttingLog_mono (Nat.le_add_right _ _))
    rw [incidences_comm Q P] at hh
    convert hh using 1; ac_rfl

end PlanarUnitDistances.CircleIncidence

namespace PlanarUnitDistances.FiniteTruncation
open Finset Classical

theorem weighted_subset {α : Type*} (s : Finset α) (w : α → ℝ)
    (hw : ∀ a ∈ s, 0 ≤ w a) {B : ℕ} (hB : 0<B) :
    ∃ t ⊆ s, t.card ≤ B ∧
      (∑ a ∈ s, w a) ≤ (1+(s.card : ℝ)/B)*(∑ a ∈ t, w a) := by
  classical
  revert hw
  refine Finset.strongInductionOn s ?_
  intro s ih hw
  have hBn : (0 : ℝ)<B := Nat.cast_pos.mpr hB
  by_cases hs : s.card ≤ B
  · refine ⟨s,Finset.Subset.refl _,hs,?_⟩
    have hn : 0 ≤ ∑ a ∈ s, w a := Finset.sum_nonneg hw
    have hc : 0 ≤ (s.card : ℝ)/B := by positivity
    nlinarith
  · obtain ⟨t,ht,htB⟩ := Finset.exists_subset_card_eq (le_of_not_ge hs)
    have htpos : t.Nonempty := Finset.card_pos.mp (by omega)
    have hss : s \ t ⊂ s := Finset.sdiff_ssubset ht htpos
    obtain ⟨u,hu,huB,huW⟩ := ih (s \ t) hss (fun a ha => hw a (Finset.mem_sdiff.mp ha).1)
    have hc : ((s \ t).card : ℝ)+(t.card : ℝ)=(s.card : ℝ) := by
      exact_mod_cast Finset.card_sdiff_add_card_eq_card ht
    have hsum : (∑ a ∈ s \ t, w a)+(∑ a ∈ t, w a)=∑ a ∈ s, w a :=
      Finset.sum_sdiff ht
    have htW : 0 ≤ ∑ a ∈ t, w a := Finset.sum_nonneg (fun a ha => hw a (ht ha))
    have huWn : 0 ≤ ∑ a ∈ u, w a :=
      Finset.sum_nonneg (fun a ha => hw a (Finset.mem_sdiff.mp (hu ha)).1)
    have hco : 0 ≤ 1+((s \ t).card : ℝ)/B := by positivity
    have he : 2+((s \ t).card : ℝ)/B=1+(s.card : ℝ)/B := by
      rw [htB] at hc
      field_simp
      linarith
    rcases le_total (∑ a ∈ u, w a) (∑ a ∈ t, w a) with h|h
    · refine ⟨t,ht,htB.le,?_⟩
      have hz := huW.trans (mul_le_mul_of_nonneg_left h hco)
      rw [← he]
      nlinarith
    · refine ⟨u,hu.trans Finset.sdiff_subset,huB,?_⟩
      rw [← he]
      nlinarith

end PlanarUnitDistances.FiniteTruncation

namespace PlanarUnitDistances.CircleIncidence
open Finset Classical CircleCutting

lemma dense_region_subset (P Q : Finset Plane) (hP : P.Nonempty)
    (D : Finset (Set Plane)) {b : ℝ} {B : ℕ} (hB : 0<B)
    (hconf : ∀ U ∈ D, ((conflicts Q U).card : ℝ) ≤ b)
    (hcover : ∀ p ∈ P, ∃ U ∈ D, p ∈ U) :
    ∃ F ⊆ P, ∃ G ⊆ Q, F.card ≤ B ∧ (G.card : ℝ) ≤ b ∧
      incidences P Q ≤ ((D.card : ℝ)+(P.card : ℝ)/B)*incidences F G := by
  choose a ham hamem using hcover
  let f (p : Plane) : Set Plane := if hp : p ∈ P then a p hp else ∅
  have hf (p : Plane) (hp : p ∈ P) : f p ∈ D ∧ p ∈ f p := by
    simpa only [f,dite_eq_left hp] using And.intro (ham p hp) (hamem p hp)
  let A (U : Set Plane) := P.filter (fun p => f p=U)
  have hA (U : Set Plane) : ∀ p ∈ A U, p ∈ U := by
    intro p hp
    obtain ⟨hp,hpU⟩ := Finset.mem_filter.mp hp
    exact hpU ▸ (hf p hp).2
  have hs (U : Set Plane) : ∃ t ⊆ A U, t.card ≤ B ∧
      incidences (A U) Q ≤ (1+((A U).card : ℝ)/B)*incidences t Q := by
    obtain ⟨t,ht,htB,htW⟩ := FiniteTruncation.weighted_subset (A U) (degree Q)
      (fun p _ => degree_nonneg Q p) hB
    refine ⟨t,ht,htB,?_⟩
    rw [incidences_comm (A U) Q,incidences_comm t Q]
    exact htW
  choose t ht htB htW using hs
  have hD : D.Nonempty := by
    obtain ⟨p,hp⟩ := hP
    exact ⟨f p,(hf p hp).1⟩
  obtain ⟨U,hU,hmax⟩ := Finset.exists_max_image D (fun U => incidences (t U) Q) hD
  refine ⟨t U,(ht U).trans (Finset.filter_subset _ _),conflicts Q U,
    Finset.filter_subset _ _,htB U,hconf U hU,?_⟩
  rw [← incidence_in_region (t U) Q U (fun p hp => hA U p (ht U hp))]
  have hsum : ∑ V ∈ D, ((A V).card : ℝ)=(P.card : ℝ) := by
    have hh := Finset.sum_fiberwise_of_maps_to (fun p hp => (hf p hp).1) (fun _ : Plane => (1 : ℝ))
    simpa only [Finset.sum_const,nsmul_eq_mul,mul_one] using hh
  have hh (V : Set Plane) (hV : V ∈ D) : incidences (A V) Q ≤
      (1+((A V).card : ℝ)/B)*incidences (t U) Q :=
    (htW V).trans (mul_le_mul_of_nonneg_left (hmax V hV) (by positivity))
  rw [← incidence_partition f (fun p hp => (hf p hp).1)]
  apply (Finset.sum_le_sum hh).trans_eq
  rw [← Finset.sum_mul,Finset.sum_add_distrib,← Finset.sum_div,hsum]
  simp

lemma deleted_incidence_trivial (P Q T : Finset Plane) (hT : T ⊆ Q) :
    incidences (deleted P T) Q ≤ (T.card : ℝ)*((P.card : ℝ)+2*Q.card) := by
  have hd := deleted_incidence_le P Q T hT
  have ht := incidences_le P T
  nlinarith

theorem exists_incidence_piece (P Q : Finset Plane) (hQ : Q.Nonempty)
    {R : ℝ} (hR : 0<R) {B : ℕ} (hB : 0<B) :
    ∃ F ⊆ P, ∃ G ⊆ Q, F.card ≤ B ∧ (G.card : ℝ) ≤ (Q.card : ℝ)/R ∧
      incidences P Q ≤ (R*cuttingLog Q.card+1)*((P.card : ℝ)+2*Q.card)+
        (43*(1+(R*cuttingLog Q.card+1)^2)+(P.card : ℝ)/B)*incidences F G := by
  obtain ⟨s,T,D,hs,hT,hTs,_,hD,hconf,hcover⟩ :=
    cutting_with_cost P Q hQ (degree P) (fun q _ => degree_nonneg P q) hR
  have hsn : (0 : ℝ) ≤ s := Nat.cast_nonneg _
  have hTl : (T.card : ℝ) ≤ R*cuttingLog Q.card+1 := (Nat.cast_le.mpr hTs).trans hs
  have hrl : 0 ≤ R*cuttingLog Q.card+1 := hsn.trans hs
  have hdel : incidences (deleted P T) Q ≤
      (R*cuttingLog Q.card+1)*((P.card : ℝ)+2*Q.card) :=
    (deleted_incidence_trivial P Q T hT).trans
      (mul_le_mul_of_nonneg_right hTl (by positivity))
  have hrP : ((retained P T).card : ℝ) ≤ (P.card : ℝ) :=
    Nat.cast_le.mpr (Finset.card_filter_le _ _)
  have hDc : (D.card : ℝ) ≤ 43*(1+(R*cuttingLog Q.card+1)^2) := by
    have hh : (D.card : ℝ) ≤ 43*(1+(s : ℝ)^2) := by exact_mod_cast hD
    have hh' := (sq_le_sq₀ hsn hrl).mpr hs
    linarith
  by_cases hp : (retained P T).Nonempty
  · obtain ⟨F,hF,G,hG,hFB,hGR,hFG⟩ := dense_region_subset (retained P T) Q hp D hB
      (fun U hU => (hconf U hU).2)
      (fun p hp => hcover p (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp).2)
    refine ⟨F,hF.trans (Finset.filter_subset _ _),G,hG,hFB,hGR,?_⟩
    have hcoef : (D.card : ℝ)+((retained P T).card : ℝ)/B ≤
        43*(1+(R*cuttingLog Q.card+1)^2)+(P.card : ℝ)/B :=
      add_le_add hDc (div_le_div_of_nonneg_right hrP (Nat.cast_nonneg _))
    have hm := mul_le_mul_of_nonneg_right hcoef (incidences_nonneg F G)
    have hsplit := incidence_deletion_split P Q T
    linarith
  · refine ⟨∅,Finset.empty_subset _,∅,Finset.empty_subset _,by simp,by simp; positivity,?_⟩
    have he : retained P T=∅ := Finset.not_nonempty_iff_eq_empty.mp hp
    have hz : incidences (retained P T) Q=0 := by simp [he,incidences,degree]
    have hz' : incidences ∅ ∅=0 := by simp [incidences]
    rw [hz',mul_zero,add_zero]
    have hsplit := incidence_deletion_split P Q T
    linarith

end PlanarUnitDistances.CircleIncidence

end OAI
