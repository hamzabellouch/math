import OAI.NumberTheory.PowerFree.DegreeSchedules

namespace OAI

open scoped BigOperators
open Matrix
open scoped BigOperators
open scoped BigOperators

namespace QuarticPowerFree

section
open MvPolynomial
open scoped BigOperators Classical
attribute [local instance] Classical.propDecidable

theorem physical_regular_half_blocks (n r E A h e : ℕ) (hr : 0 < r) (d : ℕ → ℕ)
    (a : Fin r → ℝ) (ha : ∀ i, 0 ≤ a i) (γ ξ w : ℝ)
    (hγ : 0 < γ) (hξ : 0 < ξ) (hw : 0 ≤ w) :
    ∃ ζ : ℝ, 0 < ζ ∧ ∃ U : Fin r → ℕ, (∀ i, ζ*(U i:ℝ) ≤ a i+2*γ) ∧
    ∃ K X₀ : ℝ, 1 ≤ K ∧ ∀ X : ℝ, X₀ < X →
      ∀ (G : KernelGeometry n), G.height ≤ X^w →
      ∀ (start : G.points → Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n),
      (∀ z, PhysicalState G h e z.val (start z)) →
    ∃ B : Fin r → Finset ℕ,
      (∀ i, (B i).card ≤ U i ∧ a i+γ ≤ ζ*((B i).card:ℝ)) ∧
      (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧
      (∀ i p, p ∈ B i → p.Prime ∧ X^ζ ≤ (p:ℝ) ∧ (p:ℝ) ≤ K*X^ζ) ∧
      (G.points.card:ℝ)/2 ≤ (Finset.univ.filter
        (PhysicalRegular (E := E) G d A h e r start B ξ)).card := by
  classical
  obtain ⟨C,hC,b,hblocks⟩ := physical_regular_blocks n d A h e r E
  let η := ξ/(4*r)
  have hη : 0 < η := div_pos hξ (by exact_mod_cast (show 0 < 4*r by omega))
  let V : ℕ := ((E+n).choose n+1)^r
  obtain ⟨T,hTlarge⟩ := exists_nat_gt (2*(V:ℝ)/η)
  have hT : 0 < T := by
    have : (0:ℝ) < T := lt_of_le_of_lt (div_nonneg (by positivity) hη.le) hTlarge
    exact_mod_cast this
  have hVT : (V:ℝ)/T ≤ η/2 := by
    have htc : (0:ℝ) < T := by exact_mod_cast hT
    apply (div_le_iff₀ htc).mpr
    have hh := (div_lt_iff₀ hη).mp hTlarge
    nlinarith
  let ζ := γ/((T:ℝ)+1)
  have hζ : 0 < ζ := div_pos hγ (by positivity)
  have hζT : ζ*T ≤ γ := by
    have he : ζ*((T:ℝ)+1) = γ := div_mul_cancel₀ _ (by positivity)
    nlinarith
  let ell := fun i => ⌊(a i+γ)/ζ⌋₊
  let U := fun i => ell i+T
  have hU (i) : ζ*(U i:ℝ) ≤ a i+2*γ :=
    (physical_block_width (a i) γ ζ T (U i) (ha i) hγ hζ hζT (by dsimp [U,ell]; omega) le_rfl).2
  let v : ℕ := ⌊((w*b+1)*(r+1:ℕ))/ζ⌋₊
  obtain ⟨N,hN⟩ := exists_nat_gt (2*(v:ℝ)/η)
  let t : ℕ := (∑ i, ell i)+T+N+1
  have hsize (i) : ell i+T < t := by
    have he : ell i ≤ ∑ j, ell j := Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    dsimp [t]
    omega
  have hbound (i) : (v:ℝ)/((t:ℝ)-(ell i+T)) ≤ η/2 := by
    have hp : (0:ℝ) < (t:ℝ)-(ell i+T) := by
      have hh : (ell i:ℝ)+T < t := by exact_mod_cast hsize i
      linarith
    have he : (ell i:ℝ) ≤ ∑ j, (ell j:ℝ) :=
      Finset.single_le_sum (fun j _ => Nat.cast_nonneg _) (Finset.mem_univ i)
    have ht : (t:ℝ) = (∑ j, (ell j:ℝ))+T+N+1 := by simp [t]
    have hn := (div_lt_iff₀ hη).mp hN
    apply (div_le_iff₀ hp).mpr
    nlinarith
  refine ⟨ζ,hζ,U,hU,2^(r*t+1),max 1 C,one_le_pow₀ (by norm_num),?_⟩
  intro X hX G hheight start hs
  have hX1 : 1 < X := lt_of_le_of_lt (le_max_left _ _) hX
  have hCX : C ≤ X := (le_max_right _ _).trans hX.le
  have hxζ : 1 ≤ X^ζ := Real.one_le_rpow hX1.le hζ.le
  obtain ⟨P,hPcard,hPdisj,hP⟩ := disjoint_prime_pools r t (X^ζ) hxζ
  obtain ⟨B,hB,hreg⟩ := hblocks G start hs r P ell T X ζ w η ξ hX1 hCX hw hheight hζ hξ
    (fun i p hp => (hP i p hp).1) (fun i p hp => (hP i p hp).2.1) hT
    (fun i => by rw [hPcard]; exact hsize i)
    (fun i => by rw [hPcard]; exact add_le_add hVT (hbound i) |>.trans_eq (by ring))
  refine ⟨B,?_,?_,?_,?_⟩
  · intro i
    refine ⟨(hB i).2.2,?_⟩
    exact (physical_block_width (a i) γ ζ T (B i).card (ha i) hγ hζ hζT
      (hB i).2.1 (hB i).2.2).1
  · intro i j hij
    exact (hPdisj i j hij).mono (hB i).1 (hB j).1
  · intro i p hp
    exact hP i p ((hB i).1 hp)
  · have he : 1-(r:ℝ)*η/ξ = 3/4 := by
      dsimp only [η]
      have hrc : (r:ℝ) ≠ 0 := by exact_mod_cast hr.ne'
      field_simp
      ring
    change (G.points.card:ℝ)/2 ≤ _
    have hr' : (3/4:ℝ)*G.points.card ≤
        (Finset.univ.filter (PhysicalRegular (E := E) G d A h e r start B ξ)).card := by
      unfold PhysicalRegular physicalPathProduct
      rw [he] at hreg
      convert hreg using 1
      congr 1
      congr 1
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    linarith [show (0:ℝ) ≤ G.points.card from Nat.cast_nonneg _]

end

open scoped BigOperators

theorem physical_small_parameters {r : ℕ} (n : ℕ) (a : Fin r → ℝ) (q : Fin r → ℕ)
    (ha : ∀ i, 0 ≤ a i) (ε : ℝ) (hε : 0 < ε) :
    ∃ γ ξ : ℝ, 0 < γ ∧ 0 < ξ ∧ ξ ≤ 1 ∧
      ξ*((∑ i, a i)+(r:ℝ)*γ) ≤ γ/2 ∧
      (∑ i, (a i+2*γ)*((q i:ℝ)+(n:ℝ)*ξ)) ≤ (∑ i, (q i:ℝ)*a i)+ε/2 := by
  classical
  let A := ∑ i, a i
  let Q := ∑ i, (q i:ℝ)
  let B := 2*Q+n*A+2*(n:ℝ)*r+1
  have hA : 0 ≤ A := Finset.sum_nonneg (fun i _ => ha i)
  have hQ : 0 ≤ Q := Finset.sum_nonneg (fun i _ => Nat.cast_nonneg _)
  have hB : 0 < B := by dsimp only [B]; positivity
  let γ := min 1 (ε/(4*B))
  have hγ : 0 < γ := lt_min zero_lt_one (div_pos hε (by positivity))
  have hγ1 : γ ≤ 1 := min_le_left _ _
  have hγB : γ*B ≤ ε/4 := by
    have hh : γ ≤ ε/(4*B) := min_le_right _ _
    have hh' := (le_div_iff₀ (by positivity : 0 < 4*B)).mp hh
    linarith
  let D := A+(r:ℝ)*γ+1
  have hD : 0 < D := by dsimp only [D]; positivity
  let ξ := min γ (γ/(4*D))
  have hξ : 0 < ξ := lt_min hγ (div_pos hγ (by positivity))
  have hξγ : ξ ≤ γ := min_le_left _ _
  have hξ1 : ξ ≤ 1 := hξγ.trans hγ1
  have hξD : ξ*D ≤ γ/4 := by
    have hh : ξ ≤ γ/(4*D) := min_le_right _ _
    have hh' := (le_div_iff₀ (by positivity : 0 < 4*D)).mp hh
    linarith
  refine ⟨γ,ξ,hγ,hξ,hξ1,?_,?_⟩
  · change ξ*(A+(r:ℝ)*γ) ≤ γ/2
    dsimp only [D] at hξD
    nlinarith
  · have he : (∑ i, (a i+2*γ)*((q i:ℝ)+(n:ℝ)*ξ)) =
        (∑ i, (q i:ℝ)*a i)+2*γ*Q+(n:ℝ)*ξ*A+2*γ*(n:ℝ)*ξ*r := by
      calc
        _ = ∑ i, ((q i:ℝ)*a i+2*γ*(q i:ℝ)+(n:ℝ)*ξ*a i+2*γ*(n:ℝ)*ξ) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = _ := by
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
            Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, A, Q]
          ring
    have ha' : (n:ℝ)*ξ*A ≤ (n:ℝ)*γ*A := by gcongr
    have hr' : 2*γ*(n:ℝ)*ξ*r ≤ 2*γ*(n:ℝ)*r := by
      calc
        _ ≤ 2*γ*(n:ℝ)*1*r := by gcongr
        _ = _ := by ring
    rw [he]
    dsimp only [B] at hγB
    nlinarith

open MvPolynomial
open scoped BigOperators Classical
attribute [local instance] Classical.propDecidable

theorem physical_affine_count (n r A e₀ : ℕ) (hr : 0 < r)
    (ω : Fin n → ℝ) (hω : ∀ j, 0 < ω j) (Cbox w : ℝ) (hCbox : 1 ≤ Cbox) (hw : 0 ≤ w)
    (a δ : Fin r → ℝ) (ha : ∀ i, 0 ≤ a i) (hδ : ∀ i, 0 < δ i)
    (hprefix : ∀ i, δ i ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin r => j.val ≤ i.val), a j)
    (ε : ℝ) (hε : 0 < ε) (c Kex : ℕ → ℝ) (hc : ∀ e, 0 ≤ c e) (hKex : ∀ e, 1 ≤ Kex e) :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ < X →
      ∀ (G : KernelGeometry n), G.height ≤ X^w →
        (∀ z ∈ G.points, ∀ j, |(z j:ℝ)| ≤ Cbox*X^(ω j)) →
      ∀ (I : Ideal (MvPolynomial (Fin n) ℂ)), I.IsPrime →
        affineDimension I ≤ r → affineDegree I ≤ e₀ →
        (∀ z ∈ G.points, PointOn I z) →
        (∀ (i : Fin r) (e : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)), J.IsPrime →
          I ≤ J → EquationLock J G.points A → affineDegree J ≤ e →
          affineDimension J = r-i.val → (∃ z ∈ G.points, PointOn J z) →
          ((G.points.filter (PointOn J)).card:ℝ) ≤ Kex e*X^(ε/4) ∨
          ∀ T : ℝ, 1 ≤ T → T^(r-i.val) / (((r-i.val).factorial:ℝ)*(δ i)^(r-i.val)) -
            c e*T^(r-i.val-1) ≤ weightedHilbert J ω T) →
        (G.points.card:ℝ) ≤ C*X^((∑ i, ((r-i.val:ℕ):ℝ)*a i)+ε) := by
  classical
  let q := fun i : Fin r => r-i.val
  obtain ⟨γ,ξ,hγ,hξ,hξ1,hloss,hexponent⟩ := physical_small_parameters n a q ha ε hε
  choose D Xcut hcut using fun (i : Fin r) (e : ℕ) => physical_weighted_descent ω hω
    (q i) (by dsimp [q]; omega) (δ i) (γ/2) (c e) Cbox (hδ i) (by linarith) (hc e) hCbox
  let chooseD : ℕ → ℕ → ℕ := fun i e => if hi : i < r then D ⟨i,hi⟩ e else 1
  let e := patchDegreeBudget n A r e₀
  obtain ⟨d,E,hd⟩ := physical_degree_schedule n A r e r chooseD
  let ed := fun i : Fin r => pathDegreeBudget n d A r e i.val
  have hd' (i : Fin r) : D i (ed i) ≤ d i.val ∧ d i.val ≤ E := by
    have hh := hd i.val i.isLt
    refine ⟨?_,hh.2⟩
    simpa only [chooseD,dite_eq_left i.isLt,ed] using hh.1.ge
  obtain ⟨ζ,hζ,U,hUwidth,K,Xpool,hK,hblocks⟩ :=
    physical_regular_half_blocks n r E A r e hr d a ha γ ξ w hγ hξ hw
  obtain ⟨Cb,hCb,hbranch⟩ := physical_branch_power_bound n d A r e U q (K+1) ξ
    (by linarith) hξ.le
  let Ke := 1+∑ i, Kex (ed i)
  have hKe : 1 ≤ Ke := by
    dsimp only [Ke]
    linarith [Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => zero_le_one.trans (hKex (ed i)))]
  have hKei (i) : Kex (ed i) ≤ Ke := by
    have hh := Finset.single_le_sum
      (fun j (_ : j ∈ Finset.univ) => zero_le_one.trans (hKex (ed j))) (Finset.mem_univ i)
    dsimp only [Ke]
    linarith
  let Lmax := patchCountBudget n A r e₀
  have hCbprod : 0 ≤ ∏ i, Cb i := Finset.prod_nonneg (fun i _ => zero_le_one.trans (hCb i))
  let C := 2*((r+1:ℕ):ℝ)*(Lmax+1)*(∏ i, Cb i)*(Ke+1)
  have hC : 0 < C := by
    dsimp only [C]
    have hp : 0 < ∏ i, Cb i := Finset.prod_pos (fun i _ => zero_lt_one.trans_le (hCb i))
    positivity
  refine ⟨C,max (max 2 Xpool) (∑ i, |Xcut i (ed i)|),hC,?_⟩
  intro X hX G hheight hbox I hI hdim hdeg hG hAlt
  let : I.IsPrime := hI
  have hX2 : 2 < X := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_left _ _)) hX
  have hX1 : 1 ≤ X := by linarith
  have hXpos : 0 < X := by linarith
  have hXp : Xpool < X := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_left _ _)) hX
  have hXc (i : Fin r) : Xcut i (ed i) < X := lt_of_le_of_lt
    ((le_abs_self _).trans ((Finset.single_le_sum (fun j _ => abs_nonneg (Xcut j (ed j)))
      (Finset.mem_univ i)).trans (le_max_right _ _))) hX
  obtain ⟨L,hL,start,hs⟩ := physical_initial_context G A r e₀ I hdim hdeg hG
  have hs' : ∀ z, PhysicalState G r e z.val (start z) := fun z => (hs z).2.1
  obtain ⟨B,hB,hdisj,hprime,hhalf⟩ := hblocks X hXp G hheight start hs'
  let M : Fin r → ℕ := fun _ => ⌈K*X^ζ⌉₊
  have hMx : 1 ≤ K*X^ζ := one_le_mul_of_one_le_of_one_le hK (Real.one_le_rpow hX1 hζ.le)
  have hM (i) : 1 ≤ M i := by
    have hh := (Nat.le_ceil (K*X^ζ)).trans' hMx
    exact_mod_cast hh
  have hMp (i) (p : ℕ) (hp : p ∈ B i) : p ≤ M i := by
    have hh := (hprime i p hp).2.2.trans (Nat.le_ceil (K*X^ζ))
    exact_mod_cast hh
  have hMb (i) : (M i:ℝ) ≤ (K+1)*X^ζ := by
    have hh := Nat.ceil_lt_add_one (show 0 ≤ K*X^ζ by linarith)
    have hx := Real.one_le_rpow hX1 hζ.le
    dsimp only [M]
    nlinarith
  let T := ⌈Ke*X^(ε/4)⌉₊
  have hTx : 1 ≤ Ke*X^(ε/4) := one_le_mul_of_one_le_of_one_le hKe
    (Real.one_le_rpow hX1 (by linarith))
  have hT : 1 ≤ T := by
    have hh := hTx.trans (Nat.le_ceil (Ke*X^(ε/4)))
    exact_mod_cast hh
  have hTb : (T:ℝ) ≤ (Ke+1)*X^(ε/4) := by
    have hh := Nat.ceil_lt_add_one (show 0 ≤ Ke*X^(ε/4) by linarith)
    have hx := Real.one_le_rpow hX1 (show 0 ≤ ε/4 by linarith)
    dsimp only [T]
    nlinarith
  let Ex : ℕ → Ideal (MvPolynomial (Fin n) ℂ) → Prop := fun _ J =>
    (G.points.filter (PointOn J)).card ≤ T
  have hmargin := physical_cumulative_margin a δ (fun i => (B i).card) γ ζ ξ ha hγ hξ.le hξ1
    hloss (fun i => (hB i).2) hprefix
  have hdesc (i : ℕ) (hi : i < r) (z : G.points)
      (hz : PhysicalRegular (E := E) G d A r e r start B ξ z)
      (hne : ¬ Ex i (physicalStateAt (E := E) G d A r e start B i z).1)
      (hdi : affineDimension (physicalStateAt (E := E) G d A r e start B i z).1 = r-i) :
      affineDimension (physicalStateAt (E := E) G d A r e start B (i+1) z).1 <
        affineDimension (physicalStateAt (E := E) G d A r e start B i z).1 := by
    let ii : Fin r := ⟨i,hi⟩
    let s := physicalStateAt (E := E) G d A r e start B i z
    have hstate := physicalStateAt_good (E := E) G d A r e start hs' B i z
    have hcontext := physicalStateAt_context (E := E) G d A r e start hs' B I
      (fun z => ⟨(hs z).2.2.1,(hs z).2.2.2⟩) i z
    have hH : ∀ T' : ℝ, 1 ≤ T' → T'^(q ii)/(((q ii).factorial:ℝ)*(δ ii)^(q ii)) -
        c (ed ii)*T'^(q ii-1) ≤ weightedHilbert s.1 ω T' := by
      rcases hAlt ii (ed ii) s.1 hstate.1.1 hcontext.1 hcontext.2 hstate.1.2.2 hdi
        ⟨z.val,z.property,hstate.2.2.2.1⟩ with hsmall | hH
      · apply False.elim
        apply hne
        have hh : ((G.points.filter (PointOn s.1)).card:ℝ) ≤ (T:ℝ) := hsmall.trans
          ((mul_le_mul_of_nonneg_right (hKei ii) (Real.rpow_nonneg hXpos.le _)).trans (Nat.le_ceil _))
        exact_mod_cast hh
      · exact hH
    let Q := (cumulativeBlockPrimes B i).filter (fun p : ℕ => ¬ (p:ℤ) ∣ eval z.val s.2.minor)
    have hprod : X^(δ ii+γ/2) ≤ ∏ p ∈ Q, (p:ℝ) :=
      (Real.rpow_le_rpow_of_exponent_le hX1 (hmargin ii)).trans
        (cumulative_good_prime_product B hdisj i (eval z.val s.2.minor) X ζ ξ hX1 hζ.le
          (fun j p hp => (hprime j p hp).2.1)
          (fun j => PhysicalRegular.bad_minor G d A r e r start B ξ z hz i hi.le j))
    rw [physicalStateAt_succ]
    apply hcut ii (ed ii) X (hXc ii) r E G d A r e i (hd' ii).1 (hd' ii).2 hbox
      z.val z.property s hstate hdi hH B Q (Finset.filter_subset _ _)
    · intro p hp
      obtain ⟨j,_,hpj⟩ := Finset.mem_biUnion.mp (Finset.mem_filter.mp hp).1
      exact (hprime j p hpj).1
    · intro p hp; exact (Finset.mem_filter.mp hp).2
    · exact hprod
  have hcount := physical_regular_count G d A r e start hs' B M ξ hξ.le L T Ex
    (fun z => (hs z).1) hT (fun z => (hs' z).1.2.1) hM
    (fun i p hp => (hprime i p hp).1) hMp hhalf hdesc (fun _ _ _ hh => hh)
  let κ := fun i : Fin r => ζ*((q i:ℝ)*(U i:ℝ)+(n:ℝ)*ξ*(U i:ℝ))
  have hκ (i) : 0 ≤ κ i := by dsimp [κ]; positivity
  have hsum : ∑ i, κ i ≤ (∑ i, (q i:ℝ)*a i)+ε/2 := by
    apply le_trans (Finset.sum_le_sum (fun i _ => ?_)) hexponent
    dsimp only [κ]
    calc
      _ = (ζ*(U i:ℝ))*((q i:ℝ)+(n:ℝ)*ξ) := by ring
      _ ≤ (a i+2*γ)*((q i:ℝ)+(n:ℝ)*ξ) :=
        mul_le_mul_of_nonneg_right (hUwidth i) (by positivity)
  have hforest := stopped_forest_power_bound L.length
    (physicalBranchAllowance n d A r e B M (fun k => ⌊ξ*(B k).card⌋₊) q)
    Cb κ hCb hκ X hX1 (hbranch X ζ hX1 hζ.le B M (fun i => (hB i).1) hMb)
  have hcount' : (G.points.card:ℝ) ≤ 2*((r+1:ℕ):ℝ)*L.length*(∏ i, Cb i)*
      X^(∑ i, κ i)*((Ke+1)*X^(ε/4)) := by
    have hh : (G.points.card:ℝ) ≤ 2*((∑ i ∈ Finset.range (r+1), L.length * ∏ j ∈ Finset.range i,
      if hj : j < r then physicalBranchAllowance n d A r e B M
        (fun k => ⌊ξ*(B k).card⌋₊) q ⟨j,hj⟩ else 1 : ℕ):ℝ)*(T:ℝ) := by
      exact_mod_cast hcount
    apply hh.trans
    have hh' := mul_le_mul (mul_le_mul_of_nonneg_left hforest (by norm_num : (0:ℝ) ≤ 2)) hTb
      (Nat.cast_nonneg T) (by positivity)
    convert hh' using 1; ring
  calc
    (G.points.card:ℝ) ≤ 2*((r+1:ℕ):ℝ)*L.length*(∏ i, Cb i)*(Ke+1)*X^((∑ i, κ i)+ε/4) := by
      rw [Real.rpow_add hXpos]
      convert hcount' using 1; ring
    _ ≤ C*X^((∑ i, κ i)+ε/4) := by
      have hL' : (L.length:ℝ) ≤ (Lmax:ℝ)+1 := by exact_mod_cast (hL.trans (Nat.le_succ Lmax))
      dsimp only [C]
      gcongr
    _ ≤ C*X^((∑ i, ((r-i.val:ℕ):ℝ)*a i)+ε) := by
      apply mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hX1 ?_) hC.le
      dsimp only [q] at hsum
      linarith

end QuarticPowerFree

end OAI
