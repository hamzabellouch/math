import OAI.NumberTheory.GaussianMoat.Model

namespace OAI

namespace GaussianMoat

def determinant (z w : GaussianInt) : ℤ := z.re * w.im - z.im * w.re

theorem determinant_mul_left (a z w : GaussianInt) :
    determinant (a * z) (a * w) = a.norm * determinant z w := by
  simp only [determinant, Zsqrtd.re_mul, Zsqrtd.im_mul, Zsqrtd.norm]
  ring

theorem norm_dvd_determinant {a z w : GaussianInt} (hz : a ∣ z) (hw : a ∣ w) :
    a.norm ∣ determinant z w := by
  obtain ⟨u, rfl⟩ := hz
  obtain ⟨v, rfl⟩ := hw
  rw [determinant_mul_left]
  exact dvd_mul_right _ _

theorem determinant_eq_zero_of_common_factor {a z w : GaussianInt}
    (hz : a ∣ z) (hw : a ∣ w) (hsmall : |determinant z w| < a.norm) :
    determinant z w = 0 := by
  by_contra hne
  have hpos : 0 < |determinant z w| := abs_pos.mpr hne
  have hdiv : a.norm ∣ |determinant z w| := (dvd_abs _ _).mpr (norm_dvd_determinant hz hw)
  have hle := Int.le_of_dvd hpos hdiv
  omega

structure SplitSieve where
  primes : Finset ℕ
  factor : ℕ → GaussianInt
  prime_mem : ∀ p ∈ primes, Nat.Prime p
  mod_four : ∀ p ∈ primes, p % 4 = 1
  factor_irreducible : ∀ p ∈ primes, Irreducible (factor p)
  factor_norm : ∀ p ∈ primes, (factor p).norm = (p : ℤ)

def SplitSieve.avoiding (s : SplitSieve) : Set GaussianInt :=
  {z | ∀ p ∈ s.primes, ¬s.factor p ∣ z ∧ ¬star (s.factor p) ∣ z}

def FiniteSieveEndpoint : Prop :=
  ∀ D : ℝ, 1 ≤ D → ∃ s : SplitSieve,
    ∀ z : ℕ → GaussianInt, (∀ t, z t ∈ s.avoiding) → Function.Injective z →
      (∀ t, dist (z (t + 1) : ℂ) (z t : ℂ) ≤ D) → False

theorem finite_box (N : ℤ) :
    {z : GaussianInt | |z.re| ≤ N ∧ |z.im| ≤ N}.Finite := by
  have hinj : Function.Injective (fun z : GaussianInt => (z.re, z.im)) := by
    intro z w h
    exact Zsqrtd.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
  have hf := (Set.finite_Icc (-N) N).prod (Set.finite_Icc (-N) N)
  apply (hf.preimage hinj.injOn).subset
  intro z hz
  exact ⟨abs_le.mp hz.1, abs_le.mp hz.2⟩

theorem finite_norm_le (N : ℤ) : {z : GaussianInt | z.norm ≤ N}.Finite := by
  apply (finite_box (|N| + 1)).subset
  intro z hz
  have heq : z.norm = z.re ^ 2 + z.im ^ 2 := by
    simp only [Zsqrtd.norm]
    ring
  have hn : N ≤ |N| := le_abs_self N
  have hn0 : 0 ≤ |N| := abs_nonneg N
  have hx : z.re ^ 2 ≤ (|N| + 1)^2 := by
    change z.norm ≤ N at hz
    nlinarith [sq_nonneg z.im, sq_nonneg (|N| : ℤ)]
  have hy : z.im ^ 2 ≤ (|N| + 1)^2 := by
    change z.norm ≤ N at hz
    nlinarith [sq_nonneg z.re, sq_nonneg (|N| : ℤ)]
  exact ⟨abs_le_of_sq_le_sq hx (by omega), abs_le_of_sq_le_sq hy (by omega)⟩

theorem finite_irreducibles_divisible (a : GaussianInt) (ha : Irreducible a) :
    {z : GaussianInt | Irreducible z ∧ a ∣ z}.Finite := by
  apply (finite_norm_le a.norm).subset
  intro z hz
  exact (Zsqrtd.norm_eq_of_associated (by decide) (ha.associated_of_dvd hz.1 hz.2)).ge

def SplitSieve.exceptions (s : SplitSieve) : Set GaussianInt :=
  {z | Irreducible z ∧ z ∉ s.avoiding}

theorem SplitSieve.exceptions_finite (s : SplitSieve) : s.exceptions.Finite := by
  have hfactor (p : ℕ) (hp : p ∈ s.primes) :
      {z : GaussianInt | Irreducible z ∧
        (s.factor p ∣ z ∨ star (s.factor p) ∣ z)}.Finite := by
    have hstar : Irreducible (star (s.factor p)) :=
      (MulEquiv.irreducible_iff (starRingAut : RingAut GaussianInt)).mpr
        (s.factor_irreducible p hp)
    simpa only [← Set.ofPred_or, and_or_left] using
      (finite_irreducibles_divisible (s.factor p) (s.factor_irreducible p hp)).union
        (finite_irreducibles_divisible (star (s.factor p)) hstar)
  apply ((s.primes.finite_toSet).biUnion hfactor).subset
  intro z hz
  obtain ⟨hzprime, hzavoid⟩ := hz
  simp only [SplitSieve.avoiding, Set.mem_ofPred_eq, not_forall, not_and, not_not] at hzavoid
  obtain ⟨p, hp, hdiv⟩ := hzavoid
  exact Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨hp, ⟨hzprime, by tauto⟩⟩⟩

theorem SplitSieve.eventually_avoiding (s : SplitSieve) (z : ℕ → GaussianInt)
    (hz : ∀ t, Irreducible (z t)) (hinj : Function.Injective z) :
    ∃ N : ℕ, ∀ t, N ≤ t → z t ∈ s.avoiding := by
  have hf : (z ⁻¹' s.exceptions).Finite := s.exceptions_finite.preimage hinj.injOn
  obtain ⟨N, hN⟩ := hf.exists_le
  refine ⟨N + 1, ?_⟩
  intro t ht
  by_contra h
  have ht' : t ∈ z ⁻¹' s.exceptions := ⟨hz t, h⟩
  have := hN t ht'
  omega

theorem main_of_finiteSieve (hsieve : FiniteSieveEndpoint) : MainEndpoint := by
  intro D z hz hinj hstep
  obtain ⟨s, hs⟩ := hsieve (max D 1) (le_max_right _ _)
  obtain ⟨N, hN⟩ := s.eventually_avoiding z hz hinj
  apply hs (fun t => z (N + t))
  · intro t
    exact hN _ (Nat.le_add_right _ _)
  · exact hinj.comp (fun _ _ h => Nat.add_left_cancel h)
  · intro t
    have hh : dist (z (N + (t + 1)) : ℂ) (z (N + t) : ℂ) ≤ D := by
      simpa only [Nat.add_assoc] using hstep (N + t)
    exact hh.trans (le_max_left _ _)

theorem norm_square_complex (z : GaussianInt) : (z.norm : ℝ) = ‖(z : ℂ)‖ ^ 2 := by
  rw [GaussianInt.intCast_real_norm, Complex.normSq_eq_norm_sq]

theorem finite_dist_le (c : GaussianInt) (D : ℝ) :
    {z : GaussianInt | dist (z : ℂ) (c : ℂ) ≤ D}.Finite := by
  let N : ℤ := ⌈D + ‖(c : ℂ)‖⌉
  apply (finite_box N).subset
  intro z hz
  change dist (z : ℂ) (c : ℂ) ≤ D at hz
  have htri : ‖(z : ℂ)‖ ≤ dist (z : ℂ) (c : ℂ) + ‖(c : ℂ)‖ := by
    simpa only [sub_add_cancel, ← dist_eq_norm] using
      norm_add_le ((z : ℂ) - (c : ℂ)) (c : ℂ)
  have hnorm : ‖(z : ℂ)‖ ≤ (N : ℝ) := by
    calc
      ‖(z : ℂ)‖ ≤ dist (z : ℂ) (c : ℂ) + ‖(c : ℂ)‖ := htri
      _ ≤ D + ‖(c : ℂ)‖ := add_le_add_left hz _
      _ ≤ (N : ℝ) := Int.le_ceil _
  constructor
  · have h := (Complex.abs_re_le_norm (z : ℂ)).trans hnorm
    rw [← GaussianInt.intCast_re, ← Int.cast_abs] at h
    exact Int.cast_le.mp h
  · have h := (Complex.abs_im_le_norm (z : ℂ)).trans hnorm
    rw [← GaussianInt.intCast_im, ← Int.cast_abs] at h
    exact Int.cast_le.mp h

theorem norm_le_of_dvd {a z : GaussianInt} (hz : z ≠ 0) (h : a ∣ z) :
    a.norm ≤ z.norm := by
  obtain ⟨w, rfl⟩ := h
  have hw : w ≠ 0 := by
    intro h
    apply hz
    rw [h, mul_zero]
  have hpos : 0 < w.norm := GaussianInt.norm_pos.mpr hw
  rw [Zsqrtd.norm_mul]
  nlinarith [GaussianInt.norm_nonneg a]

theorem not_dvd_sub_of_dist_sq_lt {a z w : GaussianInt} (hzw : z ≠ w)
    (hshort : dist (z : ℂ) (w : ℂ) ^ 2 < (a.norm : ℝ)) : ¬a ∣ z - w := by
  intro hdiv
  have hnorm := norm_le_of_dvd (sub_ne_zero.mpr hzw) hdiv
  have hreal : (a.norm : ℝ) ≤ ((z - w).norm : ℝ) := by exact_mod_cast hnorm
  rw [norm_square_complex (z - w), GaussianInt.toComplex_sub, ← dist_eq_norm] at hreal
  exact (not_lt_of_ge hreal) hshort

noncomputable def latticeGraph (A : Set GaussianInt) (D : ℝ) : SimpleGraph GaussianInt where
  Adj z w := z ≠ w ∧ z ∈ A ∧ w ∈ A ∧ dist (z : ℂ) (w : ℂ) ≤ D
  symm := by
    constructor
    intro z w h
    exact ⟨h.1.symm, h.2.2.1, h.2.1, by simpa only [dist_comm] using h.2.2.2⟩
  loopless := by
    constructor
    intro z h
    exact h.1 rfl

theorem lattice_walk_mem {A : Set GaussianInt} {D : ℝ} {z w : GaussianInt}
    (p : (latticeGraph A D).Walk z w) (hz : z ∈ A) (i : ℕ) : p.getVert i ∈ A := by
  induction p generalizing i with
  | nil => simpa using hz
  | @cons u v w huv p ih =>
    cases i with
    | zero => simpa using hz
    | succ i => exact ih huv.2.2.1 i

theorem lattice_walk_dist {A : Set GaussianInt} {D : ℝ} {z w : GaussianInt}
    (p : (latticeGraph A D).Walk z w) :
    dist (z : ℂ) (w : ℂ) ≤ (p.length : ℝ) * max D 0 := by
  induction p with
  | nil => simp
  | @cons u v w huv p ih =>
    calc
      dist (u : ℂ) (w : ℂ) ≤ dist (u : ℂ) (v : ℂ) + dist (v : ℂ) (w : ℂ) :=
        dist_triangle _ _ _
      _ ≤ D + (p.length : ℝ) * max D 0 := add_le_add huv.2.2.2 ih
      _ ≤ ((p.cons huv).length : ℝ) * max D 0 := by
        simp only [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one]
        nlinarith [le_max_left D 0]

@[ext]
structure LatticePrefix (A : Set GaussianInt) (D : ℝ) (root : GaussianInt) (n : ℕ) where
  point : Fin (n + 1) → GaussianInt
  mem : ∀ i, point i ∈ A
  start : point 0 = root
  injective : Function.Injective point
  step : ∀ i j, j.val = i.val + 1 → dist (point j : ℂ) (point i : ℂ) ≤ D

theorem LatticePrefix.dist_le {A : Set GaussianInt} {D : ℝ} {root : GaussianInt}
    {n : ℕ} (p : LatticePrefix A D root n) (i : Fin (n + 1)) :
    dist (p.point i : ℂ) (root : ℂ) ≤ (i.val : ℝ) * max D 0 := by
  induction i using Fin.induction with
  | zero => simp [p.start]
  | succ i ih =>
    calc
      dist (p.point i.succ : ℂ) (root : ℂ) ≤
          dist (p.point i.succ : ℂ) (p.point i.castSucc : ℂ) +
            dist (p.point i.castSucc : ℂ) (root : ℂ) := dist_triangle _ _ _
      _ ≤ D + (i.val : ℝ) * max D 0 := add_le_add (p.step _ _ rfl) ih
      _ ≤ (i.succ.val : ℝ) * max D 0 := by
        simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one]
        nlinarith [le_max_left D 0]

instance LatticePrefix.finite (A : Set GaussianInt) (D : ℝ) (root : GaussianInt) (n : ℕ) :
    Finite (LatticePrefix A D root n) := by
  let S : Set (Fin (n + 1) → GaussianInt) :=
    {f | ∀ i, dist (f i : ℂ) (root : ℂ) ≤ (n : ℝ) * max D 0}
  have hS : S.Finite := Set.Finite.pi' (fun _ => finite_dist_le root ((n : ℝ) * max D 0))
  let := hS.to_subtype
  let f : LatticePrefix A D root n → S := fun p => ⟨p.point, fun i =>
    (p.dist_le i).trans (mul_le_mul_of_nonneg_right
      (by exact_mod_cast Nat.le_of_lt_succ i.isLt) (le_max_right D 0))⟩
  exact Finite.of_injective f (fun p q h => LatticePrefix.ext (congrArg Subtype.val h))

def LatticePrefix.restrict {A : Set GaussianInt} {D : ℝ} {root : GaussianInt}
    {n m : ℕ} (h : n ≤ m) (p : LatticePrefix A D root m) : LatticePrefix A D root n where
  point i := p.point (Fin.castLE (by omega) i)
  mem i := p.mem _
  start := by simpa using p.start
  injective := p.injective.comp (Fin.castLE_injective (by omega))
  step i j hij := p.step _ _ hij

theorem infinite_component_has_walk {A : Set GaussianInt} {D : ℝ} {root : GaussianInt}
    (hroot : root ∈ A) (hinfinite : {w | (latticeGraph A D).Reachable root w}.Infinite) :
    ∃ z : ℕ → GaussianInt, (∀ n, z n ∈ A) ∧ Function.Injective z ∧
      ∀ n, dist (z (n + 1) : ℂ) (z n : ℂ) ≤ D := by
  classical
  have hne (n : ℕ) : Nonempty (LatticePrefix A D root n) := by
    have hnot : ¬ {w | (latticeGraph A D).Reachable root w} ⊆
        {w | dist (w : ℂ) (root : ℂ) ≤ (n : ℝ) * max D 0} := by
      intro h
      exact hinfinite ((finite_dist_le root ((n : ℝ) * max D 0)).subset h)
    obtain ⟨w, hw, hfar⟩ := Set.not_subset.mp hnot
    apply hw.elim_path
    intro path
    let p := path.val
    have hn : n ≤ p.length := by
      by_contra hn
      have hlen : (p.length : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : p.length ≤ n)
      have hdist := (lattice_walk_dist p).trans
        (mul_le_mul_of_nonneg_right hlen (le_max_right D 0))
      apply hfar
      change dist (w : ℂ) (root : ℂ) ≤ (n : ℝ) * max D 0
      simpa only [dist_comm] using hdist
    exact ⟨{
      point := fun i => p.getVert i.val
      mem := fun i => lattice_walk_mem p hroot _
      start := p.getVert_zero
      injective := fun i j h => Fin.ext (path.isPath.getVert_injOn
        (show i.val ≤ p.length from (Nat.le_of_lt_succ i.isLt).trans hn)
        (show j.val ≤ p.length from (Nat.le_of_lt_succ j.isLt).trans hn) h)
      step := fun i j h => by
        have hadj := p.adj_getVert_succ (i := i.val) (by omega)
        simpa only [h, dist_comm] using hadj.2.2.2
    }⟩
  let (n : ℕ) : Nonempty (LatticePrefix A D root n) := hne n
  obtain ⟨p, hp⟩ := exists_seq_forall_proj_of_forall_finite
    (α := fun n => LatticePrefix A D root n)
    (fun h => LatticePrefix.restrict h)
    (by intro n a; apply LatticePrefix.ext; funext i; rfl)
    (by intro i j k hij hjk a; apply LatticePrefix.ext; funext l; rfl)
    (fun _ _ => Set.toFinite _)
  let z : ℕ → GaussianInt := fun n => (p n).point (Fin.last n)
  have hagree (n k : ℕ) (hnk : n ≤ k) :
      (p k).point ⟨n, by omega⟩ = z n := by
    simpa only [LatticePrefix.restrict, z, Fin.last, Fin.castLE] using
      congrArg (fun a : LatticePrefix A D root n => a.point (Fin.last n)) (hp hnk)
  refine ⟨z, fun n => (p n).mem _, ?_, ?_⟩
  · intro n m heq
    have h := (hagree n (max n m) (le_max_left _ _)).trans
      (heq.trans (hagree m (max n m) (le_max_right _ _)).symm)
    exact congrArg Fin.val ((p (max n m)).injective h)
  · intro n
    have h := (p (n + 1)).step ⟨n, by omega⟩ (Fin.last (n + 1)) rfl
    simpa only [hagree n (n + 1) (by omega)] using h

theorem lattice_component_finite {A : Set GaussianInt} {D : ℝ}
    (hno : ∀ z : ℕ → GaussianInt, (∀ n, z n ∈ A) → Function.Injective z →
      (∀ n, dist (z (n + 1) : ℂ) (z n : ℂ) ≤ D) → False)
    {root : GaussianInt} (hroot : root ∈ A) :
    {w | (latticeGraph A D).Reachable root w}.Finite := by
  by_contra h
  obtain ⟨z, hz, hinj, hstep⟩ := infinite_component_has_walk hroot h
  exact hno z hz hinj hstep

def latticeTranslation {A : Set GaussianInt} {D : ℝ} (v : GaussianInt)
    (hv : ∀ z ∈ A, z + v ∈ A) :
    latticeGraph A D →g latticeGraph A D where
  toFun z := z + v
  map_rel' := by
    intro z w h
    refine ⟨fun he => h.1 (add_right_cancel he), hv z h.2.1, hv w h.2.2.1, ?_⟩
    simpa only [map_add, dist_add_right] using h.2.2.2

theorem eq_of_finite_component_period {A : Set GaussianInt} {D : ℝ}
    {root x y v : GaussianInt}
    (hfinite : {w | (latticeGraph A D).Reachable root w}.Finite)
    (hx : (latticeGraph A D).Reachable root x)
    (hy : (latticeGraph A D).Reachable root y)
    (hv : ∀ z ∈ A, z + v ∈ A) (hxy : y = x + v) : x = y := by
  classical
  by_contra hne
  have hv0 : v ≠ 0 := by intro h; apply hne; simpa [h] using hxy.symm
  have hreach : (latticeGraph A D).Reachable x (x + v) := by
    rw [← hxy]
    exact hx.symm.trans hy
  have hall (n : ℕ) : (latticeGraph A D).Reachable x (x + n • v) := by
    induction n with
    | zero => simp
    | succ n ih =>
      have ht := ih.map (latticeTranslation v hv)
      have hh := hreach.trans ht
      change (latticeGraph A D).Reachable x ((x + n • v) + v) at hh
      simpa only [succ_nsmul, add_assoc] using hh
  have hinj : Function.Injective (fun n : ℕ => x + n • v) := by
    intro n m h
    have hh := add_left_cancel h
    simp only [nsmul_eq_mul] at hh
    exact Nat.cast_injective (mul_right_cancel₀ hv0 hh)
  apply (Set.infinite_range_of_injective hinj)
  exact hfinite.subset (by rintro _ ⟨n, rfl⟩; exact hx.trans (hall n))

def SplitSieve.period (s : SplitSieve) : ℕ := ∏ p ∈ s.primes, p

theorem SplitSieve.period_pos (s : SplitSieve) : 0 < s.period := by
  exact Finset.prod_pos (fun p hp => (s.prime_mem p hp).pos)

theorem SplitSieve.factor_dvd_period (s : SplitSieve) {p : ℕ} (hp : p ∈ s.primes) :
    s.factor p ∣ (s.period : GaussianInt) ∧ star (s.factor p) ∣ (s.period : GaussianInt) := by
  have hn : (p : GaussianInt) = s.factor p * star (s.factor p) := by
    rw [← Zsqrtd.norm_eq_mul_conj, s.factor_norm p hp]
    simp
  have hd : (p : GaussianInt) ∣ (s.period : GaussianInt) := by
    have hh : p ∣ s.period := Finset.dvd_prod_of_mem (fun p : ℕ => p) hp
    exact map_dvd (Nat.castRingHom GaussianInt) hh
  constructor
  · apply dvd_trans _ hd
    rw [hn]
    exact dvd_mul_right _ _
  · apply dvd_trans _ hd
    rw [hn]
    exact dvd_mul_left _ _

theorem SplitSieve.periodic (s : SplitSieve) (z v : GaussianInt) (hz : z ∈ s.avoiding) :
    z + (s.period : GaussianInt) * v ∈ s.avoiding := by
  intro p hp
  have hd := s.factor_dvd_period hp
  constructor
  · intro h
    apply (hz p hp).1
    have hh := dvd_sub h (dvd_mul_of_dvd_left hd.1 v)
    simpa only [add_sub_cancel_right] using hh
  · intro h
    apply (hz p hp).2
    have hh := dvd_sub h (dvd_mul_of_dvd_left hd.2 v)
    simpa only [add_sub_cancel_right] using hh

def residue (Q : ℕ) (z : GaussianInt) : ZMod Q × ZMod Q := (z.re, z.im)

theorem eq_add_period_of_residue_eq {Q : ℕ} {x y : GaussianInt}
    (h : residue Q x = residue Q y) :
    ∃ v : GaussianInt, y = x + (Q : GaussianInt) * v := by
  have hx := (ZMod.intCast_eq_intCast_iff_dvd_sub x.re y.re Q).mp (congrArg Prod.fst h)
  have hy := (ZMod.intCast_eq_intCast_iff_dvd_sub x.im y.im Q).mp (congrArg Prod.snd h)
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  refine ⟨⟨a, b⟩, ?_⟩
  ext <;> simp only [Zsqrtd.re_add, Zsqrtd.im_add, Zsqrtd.re_mul, Zsqrtd.im_mul,
    Zsqrtd.re_natCast, Zsqrtd.im_natCast, zero_mul, mul_zero, add_zero] <;> omega

theorem periodic_component_bound {A : Set GaussianInt} {D : ℝ} {Q : ℕ} (hQ : Q ≠ 0)
    (hperiod : ∀ z ∈ A, ∀ v : GaussianInt, z + (Q : GaussianInt) * v ∈ A)
    {root : GaussianInt}
    (hfinite : {w | (latticeGraph A D).Reachable root w}.Finite) :
    {w | (latticeGraph A D).Reachable root w}.ncard ≤ Q ^ 2 := by
  classical
  let : NeZero Q := ⟨hQ⟩
  let C := {w | (latticeGraph A D).Reachable root w}
  have hinj : Set.InjOn (residue Q) C := by
    intro x hx y hy heq
    obtain ⟨v, hv⟩ := eq_add_period_of_residue_eq heq
    exact eq_of_finite_component_period hfinite hx hy
      (fun z hz => hperiod z hz v) hv
  have hcard := Set.ncard_le_card ((residue Q) '' C)
  rw [Set.InjOn.ncard_image hinj, Nat.card_prod, Nat.card_zmod, pow_two] at *
  exact hcard

def SplitSieve.boundary (s : SplitSieve) (D : ℝ) : Set GaussianInt :=
  {z | z ∈ s.avoiding ∧ ∃ e ∈ s.exceptions, dist (z : ℂ) (e : ℂ) ≤ D}

theorem SplitSieve.boundary_finite (s : SplitSieve) (D : ℝ) : (s.boundary D).Finite := by
  apply (s.exceptions_finite.biUnion (fun e _ => finite_dist_le e D)).subset
  rintro z ⟨_, e, he, hd⟩
  exact Set.mem_iUnion.mpr ⟨e, Set.mem_iUnion.mpr ⟨he, hd⟩⟩

def SplitSieve.restored (s : SplitSieve) (D : ℝ) : Set GaussianInt :=
  s.exceptions ∪ ⋃ v ∈ s.boundary D, {w | (latticeGraph s.avoiding D).Reachable v w}

theorem SplitSieve.restored_finite (s : SplitSieve) (D : ℝ)
    (hf : ∀ r ∈ s.avoiding, {w | (latticeGraph s.avoiding D).Reachable r w}.Finite) :
    (s.restored D).Finite := by
  exact s.exceptions_finite.union ((s.boundary_finite D).biUnion (fun _ hv => hf _ hv.1))

theorem lattice_reachable_mem {A : Set GaussianInt} {D : ℝ} {r w : GaussianInt}
    (hr : r ∈ A) (h : (latticeGraph A D).Reachable r w) : w ∈ A := by
  apply h.elim
  intro p
  simpa only [p.getVert_length] using lattice_walk_mem p hr p.length

theorem SplitSieve.restored_closed (s : SplitSieve) (D : ℝ)
    {p q : PrimeVertex} (hp : p.val ∈ s.restored D) (hadj : (primeGraph D).Adj p q) :
    q.val ∈ s.restored D := by
  classical
  by_cases hqa : q.val ∈ s.avoiding
  · rcases hp with hpe | hp
    · exact Or.inr (Set.mem_iUnion.mpr ⟨q.val, Set.mem_iUnion.mpr
        ⟨⟨hqa, p.val, hpe, by simpa only [dist_comm] using hadj.2⟩,
          SimpleGraph.Reachable.refl _⟩⟩)
    · obtain ⟨v, hv⟩ := Set.mem_iUnion.mp hp
      obtain ⟨hvb, hvp⟩ := Set.mem_iUnion.mp hv
      have hpa := lattice_reachable_mem hvb.1 hvp
      have hed : (latticeGraph s.avoiding D).Adj p.val q.val :=
        ⟨fun h => hadj.1 (Subtype.ext h), hpa, hqa, hadj.2⟩
      exact Or.inr (Set.mem_iUnion.mpr ⟨v, Set.mem_iUnion.mpr ⟨hvb,
        hvp.trans hed.reachable⟩⟩)
  · exact Or.inl ⟨q.property, hqa⟩

theorem prime_reachable_mem {D : ℝ} {T : Set GaussianInt}
    (hclosed : ∀ p q : PrimeVertex, p.val ∈ T → (primeGraph D).Adj p q → q.val ∈ T)
    {p q : PrimeVertex} (hp : p.val ∈ T) (h : (primeGraph D).Reachable p q) : q.val ∈ T := by
  apply h.elim
  intro w
  clear h
  induction w with
  | nil => exact hp
  | @cons a b c hab w ih => exact ih (hclosed a b hp hab)

theorem lattice_component_eq_singleton {A : Set GaussianInt} {D : ℝ} {r : GaussianInt}
    (hr : r ∉ A) : {w | (latticeGraph A D).Reachable r w} = {r} := by
  ext w
  constructor
  · intro h
    apply h.elim
    intro p
    cases p with
    | nil => rfl
    | cons hed p => exact (hr hed.2.1).elim
  · intro h
    rw [Set.mem_singleton_iff] at h
    subst w
    exact SimpleGraph.Reachable.refl _

theorem SplitSieve.component_subset (s : SplitSieve) (D : ℝ) (p : PrimeVertex) :
    Subtype.val '' component D p ⊆
      {w | (latticeGraph s.avoiding D).Reachable p.val w} ∪ s.restored D := by
  rintro _ ⟨q, hq, rfl⟩
  apply prime_reachable_mem (T :=
    {w | (latticeGraph s.avoiding D).Reachable p.val w} ∪ s.restored D) _
    (Or.inl (SimpleGraph.Reachable.refl _)) hq
  intro a b ha hab
  rcases ha with ha | ha
  · by_cases hpa : p.val ∈ s.avoiding
    · by_cases hba : b.val ∈ s.avoiding
      · exact Or.inl (ha.trans (show (latticeGraph s.avoiding D).Adj a.val b.val from
          ⟨fun hh => hab.1 (Subtype.ext hh), lattice_reachable_mem hpa ha, hba, hab.2⟩).reachable)
      · exact Or.inr (Or.inl ⟨b.property, hba⟩)
    · have hap : a.val = p.val := by
        have hh : a.val ∈ {w | (latticeGraph s.avoiding D).Reachable p.val w} := ha
        rw [lattice_component_eq_singleton hpa] at hh
        exact hh
      exact Or.inr (s.restored_closed D (Or.inl (by simpa only [hap] using
        (show p.val ∈ s.exceptions from ⟨p.property, hpa⟩))) hab)
  · exact Or.inr (s.restored_closed D ha hab)

theorem prime_components_of_finiteSieve (hsieve : FiniteSieveEndpoint) (D : ℝ) :
    ∃ B : ℕ, ∀ p : PrimeVertex, (component D p).Finite ∧ (component D p).ncard ≤ B := by
  classical
  obtain ⟨s, hs⟩ := hsieve (max D 1) (le_max_right _ _)
  have hno : ∀ z : ℕ → GaussianInt, (∀ n, z n ∈ s.avoiding) → Function.Injective z →
      (∀ n, dist (z (n + 1) : ℂ) (z n : ℂ) ≤ D) → False := by
    intro z hz hinj hstep
    exact hs z hz hinj (fun n => (hstep n).trans (le_max_left _ _))
  have hf (r : GaussianInt) : {w | (latticeGraph s.avoiding D).Reachable r w}.Finite := by
    by_cases hr : r ∈ s.avoiding
    · exact lattice_component_finite hno hr
    · rw [lattice_component_eq_singleton hr]
      exact Set.finite_singleton _
  have hK := s.restored_finite D (fun r _ => hf r)
  refine ⟨s.period ^ 2 + (s.restored D).ncard, fun p => ?_⟩
  let C := {w | (latticeGraph s.avoiding D).Reachable p.val w}
  have hC : C.ncard ≤ s.period ^ 2 := periodic_component_bound
    (Nat.ne_of_gt s.period_pos) (fun z hz v => s.periodic z v hz) (hf p.val)
  have hsubset := s.component_subset D p
  have hfinimage := ((hf p.val).union hK).subset hsubset
  have hfin : (component D p).Finite := by
    apply (hfinimage.preimage Subtype.val_injective.injOn).subset
    intro q hq
    exact ⟨q, hq, rfl⟩
  refine ⟨hfin, ?_⟩
  have hle := (Set.ncard_le_ncard hsubset ((hf p.val).union hK)).trans
    (Set.ncard_union_le C (s.restored D))
  rw [Set.InjOn.ncard_image Subtype.val_injective.injOn] at hle
  exact hle.trans (Nat.add_le_add_right hC _)

theorem finite_prime_walk_bound {D : ℝ} {B : ℕ}
    (hB : ∀ p : PrimeVertex, (component D p).Finite ∧ (component D p).ncard ≤ B)
    (n : ℕ) (z : Fin n → GaussianInt) (hz : ∀ i, Irreducible (z i))
    (hinj : Function.Injective z)
    (hstep : ∀ i j : Fin n, j.val = i.val + 1 → dist (z j : ℂ) (z i : ℂ) ≤ D) : n ≤ B := by
  classical
  cases n with
  | zero => exact Nat.zero_le _
  | succ n =>
    let f : Fin (n + 1) → PrimeVertex := fun i => ⟨z i, hz i⟩
    have hf : Function.Injective f := fun i j h => hinj (congrArg Subtype.val h)
    have hreach (i : Fin (n + 1)) : (primeGraph D).Reachable (f 0) (f i) := by
      induction i using Fin.induction with
      | zero => exact SimpleGraph.Reachable.refl _
      | succ i ih =>
        apply ih.trans
        apply SimpleGraph.Adj.reachable
        exact ⟨fun h => (by have hh := congrArg Fin.val (hf h); simp at hh),
          by simpa only [dist_comm] using hstep i.castSucc i.succ rfl⟩
    have hsubset : Set.range f ⊆ component D (f 0) := by
      rintro _ ⟨i, rfl⟩
      exact hreach i
    have hle := (Set.ncard_le_ncard hsubset (hB _).1).trans (hB _).2
    simpa only [Set.ncard_range_of_injective hf, Nat.card_fin] using hle

theorem endpoints_of_finiteSieve (hsieve : FiniteSieveEndpoint) : MainEndpoint ∧ UniformEndpoint := by
  refine ⟨main_of_finiteSieve hsieve, fun D => ?_⟩
  obtain ⟨B, hB⟩ := prime_components_of_finiteSieve hsieve D
  exact ⟨B, hB, finite_prime_walk_bound hB⟩

end GaussianMoat

end OAI
