import OAI.GroupTheory.Hyperbolic.DiscreteMetric

namespace OAI

namespace Release075.Discrete
variable {V : Type} {M : Metric V}

def GeodesicSpace (M : Metric V) : Prop := ∀ a b, ∃ p : Path M a b, p.Geodesic

noncomputable def shortPath (h : GeodesicSpace M) (a b : V) : Path M a b := (h a b).choose

theorem shortPath_geodesic (h : GeodesicSpace M) (a b : V) : (shortPath h a b).Geodesic :=
  (h a b).choose_spec

@[simp] theorem shortPath_length (h : GeodesicSpace M) (a b : V) :
    (shortPath h a b).length = M.dist a b := shortPath_geodesic h a b

namespace Path
variable {a b c : V}

def Outside (p : Path M a b) (o : V) (T : ℕ) : Prop := ∀ x, p.Mem x → T ≤ M.dist o x

theorem Outside.append {p : Path M a b} {q : Path M b c} {o : V} {T : ℕ}
    (hp : p.Outside o T) (hq : q.Outside o T) : (p.append q).Outside o T := by
  intro x hx
  rcases (p.mem_append_iff q x).mp hx with hx | hx
  · exact hp x hx
  · exact hq x hx

theorem Outside.reverse {p : Path M a b} {o : V} {T : ℕ}
    (hp : p.Outside o T) : p.reverse.Outside o T := by
  intro x hx
  exact hp x ((p.mem_reverse_iff x).mp hx)

theorem Outside.sub {p : Path M a b} {o : V} {T i j : ℕ}
    (hp : p.Outside o T) (hij : i ≤ j) (hj : j ≤ p.length) :
    (p.sub i j hij hj).Outside o T := by
  intro x hx
  exact hp x (p.mem_sub hij hj hx)

theorem outside_of_start (p : Path M a b) {o : V} {T : ℕ}
    (h : T+p.length ≤ M.dist o a) : p.Outside o T := by
  intro x hx
  have h₁ := p.dist_start_mem hx
  have h₂ := M.triangle o x a
  rw [M.symm x a] at h₂
  omega

theorem outside_of_end (p : Path M a b) {o : V} {T : ℕ}
    (h : T+p.length ≤ M.dist o b) : p.Outside o T := by
  intro x hx
  have h₁ := p.dist_end_mem hx
  have h₂ := M.triangle o x b
  rw [M.symm x b] at h₂
  omega

theorem triangle_lengths {p : Path M a b} {q : Path M b c} {s : Path M a c}
    (hp : p.Geodesic) (hq : q.Geodesic) (hs : s.Geodesic) :
    p.length ≤ q.length+s.length ∧ q.length ≤ p.length+s.length ∧
      s.length ≤ p.length+q.length := by
  have h₁ := M.triangle a c b
  have h₂ := M.triangle b a c
  have h₃ := M.triangle a b c
  rw [M.symm c b] at h₁
  rw [M.symm b a] at h₂
  change p.length = M.dist a b at hp
  change q.length = M.dist b c at hq
  change s.length = M.dist a c at hs
  omega

/-- Localization in a long arm of the comparison tripod. -/
theorem shortBypass_arm (hgeo : GeodesicSpace M)
    {p : Path M a b} {q : Path M b c} {s : Path M a c}
    (hp : p.Geodesic) (hq : q.Geodesic) (hs : s.Geodesic)
    {T R t : ℕ} (hR : 4*T+2 ≤ R) (ht : t ≤ p.length)
    (hthin : SideNear T p q s)
    (hfar : ∀ x, q.Mem x ∨ s.Mem x → T ≤ M.dist (p.point t) x)
    (harm : t+4*R < (p.length+s.length-q.length)/2) :
    ShortBypass M T (p.point t) (10*R) := by
  obtain ⟨hA,hB,hC⟩ := triangle_lengths hp hq hs
  let l := t-2*R
  let u := t+2*R
  have hlu : l ≤ u := by dsimp [l,u]; omega
  have huα : u ≤ (p.length+s.length-q.length)/2 := by dsimp [u]; omega
  have hlα : l ≤ (p.length+s.length-q.length)/2 := hlu.trans huα
  have huA : u ≤ p.length := by omega
  have huC : u ≤ s.length := by omega
  have hlt : l ≤ t := Nat.sub_le _ _
  have htu : t ≤ u := by dsimp [u]; omega
  let A := p.sub l u hlu huA
  let S := s.sub l u hlu huC
  let U := shortPath hgeo (p.point u) (s.point u)
  let L := shortPath hgeo (s.point l) (p.point l)
  have hU : U.length ≤ R := by
    rw [show U.length = M.dist (p.point u) (s.point u) from shortPath_length hgeo _ _]
    exact (synchronous hp hq hs hthin huα).trans hR
  have hL : L.length ≤ R := by
    rw [show L.length = M.dist (s.point l) (p.point l) from shortPath_length hgeo _ _,M.symm]
    exact (synchronous hp hq hs hthin hlα).trans hR
  have outU : U.Outside (p.point t) T := by
    apply U.outside_of_start
    rw [p.geodesic_dist_at hp htu huA]
    dsimp [u]
    omega
  have outL : L.Outside (p.point t) T := by
    apply L.outside_of_end
    by_cases hl : l = 0
    · have hL0 : L.length = 0 := by
        change (shortPath hgeo (s.point l) (p.point l)).length = 0
        rw [shortPath_length,hl,p.zero,s.zero,M.self]
      have h := hfar a (Or.inr s.start_mem)
      simpa only [hL0,Nat.add_zero,hl,p.zero] using h
    · rw [M.symm (p.point t) (p.point l),p.geodesic_dist_at hp hlt ht]
      dsimp [l] at *
      omega
  have outS : S.reverse.Outside (p.point t) T := by
    apply Outside.reverse
    exact (show s.Outside (p.point t) T from fun x hx => hfar x (Or.inr hx)).sub hlu huC
  refine ⟨p.point l,p.point u,A,(U.append S.reverse).append L,
    p.geodesic_sub hp hlu huA,?_,(outU.append outS).append outL,?_⟩
  · refine ⟨t-l,?_,?_⟩
    · change t-l ≤ u-l
      omega
    · rw [show A.point (t-l) = p.point (l+(t-l)) from p.sub_at hlu huA (by omega)]
      rw [Nat.add_sub_of_le hlt]
  · change (u-l)+(U.length+(u-l)+L.length) ≤ 10*R
    dsimp [u,l]
    omega

/-- Localization near the three-pronged center of the comparison tripod. -/
theorem shortBypass_center (hgeo : GeodesicSpace M)
    {p : Path M a b} {q : Path M b c} {s : Path M a c}
    (hp : p.Geodesic) (hq : q.Geodesic) (hs : s.Geodesic)
    {T R t : ℕ} (hR : 4*T+2 ≤ R) (ht : t ≤ p.length)
    (hthin : TriangleNear T p q s)
    (hfar : ∀ x, q.Mem x ∨ s.Mem x → T ≤ M.dist (p.point t) x)
    (hcenter₁ : (p.length+s.length-q.length)/2 ≤ t+4*R)
    (hcenter₂ : (p.length+q.length-s.length)/2 ≤ p.length-t+4*R) :
    ShortBypass M T (p.point t) (60*R) := by
  obtain ⟨hA,hB,hC⟩ := triangle_lengths hp hq hs
  let α := (p.length+s.length-q.length)/2
  let β := (p.length+q.length-s.length)/2
  let γ := (q.length+s.length-p.length)/2
  have hcoords : α+β ≤ p.length ∧ p.length ≤ α+β+1 ∧
      β+γ ≤ q.length ∧ q.length ≤ β+γ+1 ∧
      α+γ ≤ s.length ∧ s.length ≤ α+γ+1 := by
    dsimp [α,β,γ]
    omega
  change α ≤ t+4*R at hcenter₁
  change β ≤ p.length-t+4*R at hcenter₂
  let x := α-8*R
  let y := β-8*R
  let z := γ-8*R
  have hxα : x ≤ α := Nat.sub_le _ _
  have hyβ : y ≤ β := Nat.sub_le _ _
  have hzγ : z ≤ γ := Nat.sub_le _ _
  have hxt : x ≤ t := by dsimp [x]; omega
  have hty : t ≤ p.length-y := by dsimp [y]; omega
  have hxp : x ≤ p.length-y := hxt.trans hty
  have hyp : p.length-y ≤ p.length := Nat.sub_le _ _
  have hyq : y ≤ q.length-z := by omega
  have hzq : q.length-z ≤ q.length := Nat.sub_le _ _
  have hxs : x ≤ s.length-z := by omega
  have hzs : s.length-z ≤ s.length := Nat.sub_le _ _
  let P := p.sub x (p.length-y) hxp hyp
  let Q := q.sub y (q.length-z) hyq hzq
  let S := s.sub x (s.length-z) hxs hzs
  let X := shortPath hgeo (s.point x) (p.point x)
  let Y := shortPath hgeo (p.point (p.length-y)) (q.point y)
  let Z := shortPath hgeo (q.point (q.length-z)) (s.point (s.length-z))
  have hX : X.length ≤ R := by
    rw [show X.length = M.dist (s.point x) (p.point x) from shortPath_length hgeo _ _,M.symm]
    exact (synchronous hp hq hs hthin.1 hxα).trans hR
  have hY : Y.length ≤ R := by
    have hn : SideNear T p.reverse s q := (hthin.1.reverse T).swap T
    have hd := synchronous (p.geodesic_reverse hp) hs hq hn hyβ
    change M.dist (p.point (p.length-y)) (q.point y) ≤ 4*T+2 at hd
    rw [show Y.length = M.dist (p.point (p.length-y)) (q.point y) from shortPath_length hgeo _ _]
    exact hd.trans hR
  have hZ : Z.length ≤ R := by
    have hn : SideNear T q.reverse p.reverse s.reverse :=
      (((hthin.2.1.swap T).reverse_left T).reverse_right T).reverse T
    have hd := synchronous (q.geodesic_reverse hq) (p.geodesic_reverse hp)
      (s.geodesic_reverse hs) hn hzγ
    change M.dist (q.point (q.length-z)) (s.point (s.length-z)) ≤ 4*T+2 at hd
    rw [show Z.length = M.dist (q.point (q.length-z)) (s.point (s.length-z))
      from shortPath_length hgeo _ _]
    exact hd.trans hR
  have outX : X.Outside (p.point t) T := by
    apply X.outside_of_end
    by_cases hx : x = 0
    · have hl : X.length = 0 := by
        change (shortPath hgeo (s.point x) (p.point x)).length = 0
        rw [shortPath_length,hx,p.zero,s.zero,M.self]
      have hf := hfar a (Or.inr s.start_mem)
      simpa only [hl,Nat.add_zero,hx,p.zero] using hf
    · rw [M.symm (p.point t) (p.point x),p.geodesic_dist_at hp hxt ht]
      dsimp [x] at *
      omega
  have outY : Y.Outside (p.point t) T := by
    apply Y.outside_of_start
    by_cases hy : y = 0
    · have hl : Y.length = 0 := by
        change (shortPath hgeo (p.point (p.length-y)) (q.point y)).length = 0
        rw [shortPath_length,hy,Nat.sub_zero,p.last,q.zero,M.self]
      have hf := hfar b (Or.inl q.start_mem)
      simpa only [hl,Nat.add_zero,hy,Nat.sub_zero,p.last] using hf
    · rw [p.geodesic_dist_at hp hty hyp]
      dsimp [y] at *
      omega
  have outZ : Z.Outside (p.point t) T := by
    apply Z.outside_of_start
    by_cases hz : z = 0
    · have hl : Z.length = 0 := by
        change (shortPath hgeo (q.point (q.length-z)) (s.point (s.length-z))).length = 0
        simp only [shortPath_length,hz,Nat.sub_zero,q.last,s.last,M.self]
      have hf := hfar c (Or.inl q.end_mem)
      simpa only [hl,Nat.add_zero,hz,Nat.sub_zero,q.last] using hf
    · have ha := M.triangle a (p.point t) c
      rw [p.geodesic_start_dist hp ht] at ha
      have hc := M.triangle (p.point t) (q.point (q.length-z)) c
      rw [q.geodesic_end_dist hq hzq] at hc
      have hzz : z ≤ q.length := by omega
      rw [Nat.sub_sub_self hzz] at hc
      change s.length = M.dist a c at hs
      dsimp [z] at *
      omega
  have outQ : Q.Outside (p.point t) T :=
    (show q.Outside (p.point t) T from fun v hv => hfar v (Or.inl hv)).sub hyq hzq
  have outS : S.reverse.Outside (p.point t) T :=
    ((show s.Outside (p.point t) T from fun v hv => hfar v (Or.inr hv)).sub hxs hzs).reverse
  refine ⟨p.point x,p.point (p.length-y),P,(((Y.append Q).append Z).append S.reverse).append X,
    p.geodesic_sub hp hxp hyp,?_,(((outY.append outQ).append outZ).append outS).append outX,?_⟩
  · refine ⟨t-x,?_,?_⟩
    · change t-x ≤ p.length-y-x
      omega
    · rw [show P.point (t-x) = p.point (x+(t-x)) from p.sub_at hxp hyp (by omega)]
      rw [Nat.add_sub_of_le hxt]
  · change (p.length-y-x)+(Y.length+(q.length-z-y)+Z.length+(s.length-z-x)+X.length) ≤ 60*R
    dsimp [x,y,z] at *
    omega

/-- A maximally fat point of a T-thin triangle has a bypass of length at most 1000(T+1). -/
theorem shortBypass_triangle (hgeo : GeodesicSpace M)
    {p : Path M a b} {q : Path M b c} {s : Path M a c}
    (hp : p.Geodesic) (hq : q.Geodesic) (hs : s.Geodesic)
    {T : ℕ} (hthin : TriangleNear T p q s) {o : V} (ho : p.Mem o)
    (hfar : ∀ x, q.Mem x ∨ s.Mem x → T ≤ M.dist o x) :
    ShortBypass M T o (1000*(T+1)) := by
  obtain ⟨t,ht,rfl⟩ := ho
  let R := 4*T+4
  have hR : 4*T+2 ≤ R := by dsimp [R]; omega
  have enlarge {K : ℕ} (hK : K ≤ 1000*(T+1))
      (h : ShortBypass M T (p.point t) K) : ShortBypass M T (p.point t) (1000*(T+1)) := by
    obtain ⟨a,b,A,Q,hA,ho,hfar,hlen⟩ := h
    exact ⟨a,b,A,Q,hA,ho,hfar,hlen.trans hK⟩
  by_cases hleft : t+4*R < (p.length+s.length-q.length)/2
  · apply enlarge (K:=10*R) (by dsimp [R]; omega)
    exact shortBypass_arm hgeo hp hq hs hR ht hthin.1 hfar hleft
  by_cases hright : p.length-t+4*R < (p.length+q.length-s.length)/2
  · have hn : SideNear T p.reverse s q := (hthin.1.reverse T).swap T
    have hr := shortBypass_arm hgeo (p.geodesic_reverse hp) hs hq hR
      (t:=p.length-t) (Nat.sub_le _ _) hn
      (fun x hx => by
        change T ≤ M.dist (p.point (p.length-(p.length-t))) x
        rw [Nat.sub_sub_self ht]
        exact hfar x hx.symm) hright
    change ShortBypass M T (p.point (p.length-(p.length-t))) (10*R) at hr
    rw [Nat.sub_sub_self ht] at hr
    exact enlarge (by dsimp [R]; omega) hr
  · apply enlarge (K:=60*R) (by dsimp [R]; omega)
    exact shortBypass_center hgeo hp hq hs hR ht hthin hfar (by omega) (by omega)

end Path

theorem quadratic_bound {B T : ℕ}
    (h : ((T/2:ℕ):ℤ)^2 ≤ (B:ℤ)*(1000*(T+1))) : T ≤ 10000*(B+1) := by
  by_contra hn
  let k := T/2
  have hk : T ≤ 2*k+1 := by dsimp [k]; omega
  have hkT : k ≤ T := Nat.div_le_self _ _
  have hT : (8000:ℤ)*B+10000 ≤ T := by omega
  have hm := mul_nonneg (sub_nonneg.mpr hT) (show (0:ℤ) ≤ (T:ℤ)+1 by omega)
  have hs : (T:ℤ)^2 ≤ (2*(k:ℤ)+1)^2 := by
    apply sq_le_sq₀ (by positivity) (by positivity) |>.mpr
    exact_mod_cast hk
  change (k:ℤ)^2 ≤ (B:ℤ)*(1000*(T+1)) at h
  have hkt : (k:ℤ) ≤ T := by exact_mod_cast hkT
  nlinarith

namespace Path
variable {a b c : V}

theorem SideNear.mono {T U : ℕ} {p : Path M a b} {q : Path M b c} {s : Path M a c}
    (h : SideNear T p q s) (hTU : T ≤ U) : SideNear U p q s := by
  intro x hx
  obtain ⟨y,hy,hd⟩ := h x hx
  exact ⟨y,hy,hd.trans hTU⟩

theorem sideNear_shrink (hgeo : GeodesicSpace M) {B T : ℕ}
    (hB : CochainBound M B) (hlarge : 10000*(B+1) < T)
    {p : Path M a b} {q : Path M b c} {s : Path M a c}
    (hp : p.Geodesic) (hq : q.Geodesic) (hs : s.Geodesic)
    (hthin : TriangleNear T p q s) : SideNear (T-1) p q s := by
  classical
  intro o ho
  by_contra hn
  have hfar : ∀ x, q.Mem x ∨ s.Mem x → T ≤ M.dist o x := by
    intro x hx
    have hnot : ¬ M.dist o x ≤ T-1 := fun h => hn ⟨x,hx,h⟩
    omega
  have hb := shortBypass_triangle hgeo hp hq hs hthin ho hfar
  have hh := quadratic_bound (shortBypass_quadratic hB hb)
  omega

theorem triangleNear_shrink (hgeo : GeodesicSpace M) {B T : ℕ}
    (hB : CochainBound M B) (hlarge : 10000*(B+1) < T)
    {p : Path M a b} {q : Path M b c} {s : Path M a c}
    (hp : p.Geodesic) (hq : q.Geodesic) (hs : s.Geodesic)
    (hthin : TriangleNear T p q s) : TriangleNear (T-1) p q s := by
  refine ⟨sideNear_shrink hgeo hB hlarge hp hq hs hthin,?_,?_⟩
  · have hn : TriangleNear T q s.reverse p.reverse :=
      ⟨(hthin.2.1.reverse_left T).reverse_right T,
        (hthin.2.2.reverse T).reverse_left T,
        (hthin.1.reverse T).reverse_right T⟩
    have hh := sideNear_shrink hgeo hB hlarge hq (s.geodesic_reverse hs)
      (p.geodesic_reverse hp) hn
    intro x hx
    obtain ⟨y,hy,hd⟩ := hh x hx
    exact ⟨y,hy.imp ((s.mem_reverse_iff y).mp) ((p.mem_reverse_iff y).mp),hd⟩
  · have hn : TriangleNear T s q.reverse p :=
      ⟨(hthin.2.2.swap T).reverse_left T,
        (hthin.2.1.swap T).reverse T,
        (hthin.1.swap T).reverse_right T⟩
    have hh := sideNear_shrink hgeo hB hlarge hs (q.geodesic_reverse hq) hp hn
    intro x hx
    obtain ⟨y,hy,hd⟩ := hh x hx
    exact ⟨y,(hy.imp ((q.mem_reverse_iff y).mp) id).symm,hd⟩

/-- Discrete linear filling implies genuine uniform thinness of geodesic triangles. -/
theorem triangleNear_of_cochainBound (hgeo : GeodesicSpace M) {B : ℕ}
    (hB : CochainBound M B) {p : Path M a b} {q : Path M b c} {s : Path M a c}
    (hp : p.Geodesic) (hq : q.Geodesic) (hs : s.Geodesic) :
    TriangleNear (10000*(B+1)) p q s := by
  classical
  have hex : ∃ T, TriangleNear T p q s := by
    refine ⟨p.length+q.length+s.length,?_,?_,?_⟩
    · intro x hx
      refine ⟨a,Or.inr s.start_mem,?_⟩
      rw [M.symm]
      exact (p.dist_start_mem hx).trans (by omega)
    · intro x hx
      refine ⟨b,Or.inr p.end_mem,?_⟩
      rw [M.symm]
      exact (q.dist_start_mem hx).trans (by omega)
    · intro x hx
      refine ⟨a,Or.inl p.start_mem,?_⟩
      rw [M.symm]
      exact (s.dist_start_mem hx).trans (by omega)
  let T := Nat.find hex
  have hthin : TriangleNear T p q s := Nat.find_spec hex
  have hT : T ≤ 10000*(B+1) := by
    by_contra hn
    have hshrink := triangleNear_shrink hgeo hB (by omega : 10000*(B+1) < T) hp hq hs hthin
    have hf := Nat.find_min' hex hshrink
    change T ≤ T-1 at hf
    omega
  exact ⟨hthin.1.mono hT,by
    intro x hx
    obtain ⟨y,hy,hd⟩ := hthin.2.1 x hx
    exact ⟨y,hy,hd.trans hT⟩,by
    intro x hx
    obtain ⟨y,hy,hd⟩ := hthin.2.2 x hx
    exact ⟨y,hy,hd.trans hT⟩⟩

end Path
end Release075.Discrete

end OAI
