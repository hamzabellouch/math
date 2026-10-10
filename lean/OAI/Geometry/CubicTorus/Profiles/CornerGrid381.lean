import Mathlib
import OAI.Geometry.CubicTorus.Profiles.CornerGrid269

namespace OAI

section
noncomputable section
namespace CubicTorus

private lemma corner_grid_381 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (19/32 : ℝ)≤t) (hu : t≤(5/8 : ℝ))
    (hd : (377/720 : ℝ)≤d) (he : d≤(13/24 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(57937/85050 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_382 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (19/32 : ℝ)≤t) (hu : t≤(5/8 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(13/24 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (377/720 : ℝ) with hm|hm
  · exact corner_grid_380 h hl hu hd hm
  · exact corner_grid_381 h hl hu hm.le he

private lemma corner_grid_383 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (9/16 : ℝ)≤t) (hu : t≤(5/8 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(13/24 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (19/32 : ℝ) with hm|hm
  · exact corner_grid_379 h hl hm hd he
  · exact corner_grid_382 h hm.le hu hd he

private lemma corner_grid_384 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (9/16 : ℝ)≤t) (hu : t≤(19/32 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(403/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(29216/41769 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_385 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (9/16 : ℝ)≤t) (hu : t≤(19/32 : ℝ))
    (hd : (403/720 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(5666408/9398025 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_386 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (9/16 : ℝ)≤t) (hu : t≤(19/32 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (403/720 : ℝ) with hm|hm
  · exact corner_grid_384 h hl hu hd hm
  · exact corner_grid_385 h hl hu hm.le he

private lemma corner_grid_387 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (19/32 : ℝ)≤t) (hu : t≤(5/8 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(110/189 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_388 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (9/16 : ℝ)≤t) (hu : t≤(5/8 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (19/32 : ℝ) with hm|hm
  · exact corner_grid_386 h hl hm hd he
  · exact corner_grid_387 h hm.le hu hd he

private lemma corner_grid_389 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (9/16 : ℝ)≤t) (hu : t≤(5/8 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (13/24 : ℝ) with hm|hm
  · exact corner_grid_383 h hl hu hd hm
  · exact corner_grid_388 h hl hu hm.le he

private lemma corner_grid_390 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/2 : ℝ)≤t) (hu : t≤(5/8 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (9/16 : ℝ) with hm|hm
  · exact corner_grid_376 h hl hm hd he
  · exact corner_grid_389 h hm.le hu hd he

private lemma corner_grid_391 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/2 : ℝ)≤t) (hu : t≤(5/8 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (91/180 : ℝ) with hm|hm
  · exact corner_grid_361 h hl hu hd hm
  · exact corner_grid_390 h hl hu hm.le he

private lemma corner_grid_392 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/8 : ℝ)≤t) (hu : t≤(21/32 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(65/144 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(86272/83475 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_393 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/8 : ℝ)≤t) (hu : t≤(21/32 : ℝ))
    (hd : (65/144 : ℝ)≤d) (he : d≤(169/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(536/567 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_394 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/8 : ℝ)≤t) (hu : t≤(21/32 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(169/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (65/144 : ℝ) with hm|hm
  · exact corner_grid_392 h hl hu hd hm
  · exact corner_grid_393 h hl hu hm.le he

private lemma corner_grid_395 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (21/32 : ℝ)≤t) (hu : t≤(11/16 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(65/144 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(197648/212625 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_396 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (21/32 : ℝ)≤t) (hu : t≤(11/16 : ℝ))
    (hd : (65/144 : ℝ)≤d) (he : d≤(169/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(63866/76545 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_397 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (21/32 : ℝ)≤t) (hu : t≤(11/16 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(169/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (65/144 : ℝ) with hm|hm
  · exact corner_grid_395 h hl hu hd hm
  · exact corner_grid_396 h hl hu hm.le he

private lemma corner_grid_398 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/8 : ℝ)≤t) (hu : t≤(11/16 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(169/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (21/32 : ℝ) with hm|hm
  · exact corner_grid_394 h hl hm hd he
  · exact corner_grid_397 h hm.le hu hd he

private lemma corner_grid_399 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/8 : ℝ)≤t) (hu : t≤(21/32 : ℝ))
    (hd : (169/360 : ℝ)≤d) (he : d≤(39/80 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(641248/751275 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_400 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/8 : ℝ)≤t) (hu : t≤(21/32 : ℝ))
    (hd : (39/80 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(7032/9275 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_401 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/8 : ℝ)≤t) (hu : t≤(21/32 : ℝ))
    (hd : (169/360 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (39/80 : ℝ) with hm|hm
  · exact corner_grid_399 h hl hu hd hm
  · exact corner_grid_400 h hl hu hm.le he

private lemma corner_grid_402 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (21/32 : ℝ)≤t) (hu : t≤(11/16 : ℝ))
    (hd : (169/360 : ℝ)≤d) (he : d≤(39/80 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(1407032/1913625 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_403 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (21/32 : ℝ)≤t) (hu : t≤(11/16 : ℝ))
    (hd : (39/80 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(2134/3375 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_404 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (21/32 : ℝ)≤t) (hu : t≤(11/16 : ℝ))
    (hd : (169/360 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (39/80 : ℝ) with hm|hm
  · exact corner_grid_402 h hl hu hd hm
  · exact corner_grid_403 h hl hu hm.le he

private lemma corner_grid_405 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/8 : ℝ)≤t) (hu : t≤(11/16 : ℝ))
    (hd : (169/360 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (21/32 : ℝ) with hm|hm
  · exact corner_grid_401 h hl hm hd he
  · exact corner_grid_404 h hm.le hu hd he

private lemma corner_grid_406 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/8 : ℝ)≤t) (hu : t≤(11/16 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (169/360 : ℝ) with hm|hm
  · exact corner_grid_398 h hl hu hd hm
  · exact corner_grid_405 h hl hu hm.le he

private lemma corner_grid_407 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/16 : ℝ)≤t) (hu : t≤(23/32 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(65/144 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(57472/70875 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_408 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/16 : ℝ)≤t) (hu : t≤(23/32 : ℝ))
    (hd : (65/144 : ℝ)≤d) (he : d≤(169/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(3608/5103 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_409 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/16 : ℝ)≤t) (hu : t≤(23/32 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(169/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (65/144 : ℝ) with hm|hm
  · exact corner_grid_407 h hl hu hd hm
  · exact corner_grid_408 h hl hu hm.le he

private lemma corner_grid_410 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (23/32 : ℝ)≤t) (hu : t≤(3/4 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(65/144 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(7403/11025 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_411 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (23/32 : ℝ)≤t) (hu : t≤(3/4 : ℝ))
    (hd : (65/144 : ℝ)≤d) (he : d≤(169/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(17677/31752 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_412 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (23/32 : ℝ)≤t) (hu : t≤(3/4 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(169/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (65/144 : ℝ) with hm|hm
  · exact corner_grid_410 h hl hu hd hm
  · exact corner_grid_411 h hl hu hm.le he

private lemma corner_grid_413 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/16 : ℝ)≤t) (hu : t≤(3/4 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(169/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (23/32 : ℝ) with hm|hm
  · exact corner_grid_409 h hl hm hd he
  · exact corner_grid_412 h hm.le hu hd he

private lemma corner_grid_414 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/16 : ℝ)≤t) (hu : t≤(23/32 : ℝ))
    (hd : (169/360 : ℝ)≤d) (he : d≤(39/80 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(382048/637875 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_415 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/16 : ℝ)≤t) (hu : t≤(23/32 : ℝ))
    (hd : (39/80 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(3832/7875 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_416 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/16 : ℝ)≤t) (hu : t≤(23/32 : ℝ))
    (hd : (169/360 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (39/80 : ℝ) with hm|hm
  · exact corner_grid_414 h hl hu hd hm
  · exact corner_grid_415 h hl hu hm.le he

private lemma corner_grid_417 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (23/32 : ℝ)≤t) (hu : t≤(3/4 : ℝ))
    (hd : (169/360 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(1771/4050 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_418 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/16 : ℝ)≤t) (hu : t≤(3/4 : ℝ))
    (hd : (169/360 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (23/32 : ℝ) with hm|hm
  · exact corner_grid_416 h hl hm hd he
  · exact corner_grid_417 h hm.le hu hd he

private lemma corner_grid_419 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/16 : ℝ)≤t) (hu : t≤(3/4 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (169/360 : ℝ) with hm|hm
  · exact corner_grid_413 h hl hu hd hm
  · exact corner_grid_418 h hl hu hm.le he

private lemma corner_grid_420 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/8 : ℝ)≤t) (hu : t≤(3/4 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (11/16 : ℝ) with hm|hm
  · exact corner_grid_406 h hl hm hd he
  · exact corner_grid_419 h hm.le hu hd he

private lemma corner_grid_421 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/8 : ℝ)≤t) (hu : t≤(21/32 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(377/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(9344/14175 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_422 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/8 : ℝ)≤t) (hu : t≤(21/32 : ℝ))
    (hd : (377/720 : ℝ)≤d) (he : d≤(13/24 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(418168/751275 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_423 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/8 : ℝ)≤t) (hu : t≤(21/32 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(13/24 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (377/720 : ℝ) with hm|hm
  · exact corner_grid_421 h hl hu hd hm
  · exact corner_grid_422 h hl hu hm.le he

private lemma corner_grid_424 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (21/32 : ℝ)≤t) (hu : t≤(11/16 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(13/24 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(1005488/1913625 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_425 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/8 : ℝ)≤t) (hu : t≤(11/16 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(13/24 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (21/32 : ℝ) with hm|hm
  · exact corner_grid_423 h hl hm hd he
  · exact corner_grid_424 h hm.le hu hd he

private lemma corner_grid_426 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/8 : ℝ)≤t) (hu : t≤(21/32 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(1504/3339 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_427 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (21/32 : ℝ)≤t) (hu : t≤(11/16 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(2552/8505 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_428 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/8 : ℝ)≤t) (hu : t≤(11/16 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (21/32 : ℝ) with hm|hm
  · exact corner_grid_426 h hl hm hd he
  · exact corner_grid_427 h hm.le hu hd he

private lemma corner_grid_429 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/8 : ℝ)≤t) (hu : t≤(11/16 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (13/24 : ℝ) with hm|hm
  · exact corner_grid_425 h hl hu hd hm
  · exact corner_grid_428 h hl hu hm.le he

private lemma corner_grid_430 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/16 : ℝ)≤t) (hu : t≤(23/32 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(13/24 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(236032/637875 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_431 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (23/32 : ℝ)≤t) (hu : t≤(3/4 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(13/24 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(18293/99225 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_432 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/16 : ℝ)≤t) (hu : t≤(3/4 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(13/24 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (23/32 : ℝ) with hm|hm
  · exact corner_grid_430 h hl hm hd he
  · exact corner_grid_431 h hm.le hu hd he

private lemma corner_grid_433 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/16 : ℝ)≤t) (hu : t≤(3/4 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(121/882 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_434 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/16 : ℝ)≤t) (hu : t≤(3/4 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (13/24 : ℝ) with hm|hm
  · exact corner_grid_432 h hl hu hd hm
  · exact corner_grid_433 h hl hu hm.le he

private lemma corner_grid_435 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/8 : ℝ)≤t) (hu : t≤(3/4 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (11/16 : ℝ) with hm|hm
  · exact corner_grid_429 h hl hm hd he
  · exact corner_grid_434 h hm.le hu hd he

private lemma corner_grid_436 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/8 : ℝ)≤t) (hu : t≤(3/4 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (91/180 : ℝ) with hm|hm
  · exact corner_grid_420 h hl hu hd hm
  · exact corner_grid_435 h hl hu hm.le he

private lemma corner_grid_437 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/2 : ℝ)≤t) (hu : t≤(3/4 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (5/8 : ℝ) with hm|hm
  · exact corner_grid_391 h hl hm hd he
  · exact corner_grid_436 h hm.le hu hd he

private lemma corner_grid_438 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/2 : ℝ)≤t) (hu : t≤(3/4 : ℝ))
    (hd : (13/45 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (13/30 : ℝ) with hm|hm
  · exact corner_grid_332 h hl hu hd hm
  · exact corner_grid_437 h hl hu hm.le he

private lemma corner_grid_439 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/4 : ℝ)≤t) (hu : t≤(25/32 : ℝ))
    (hd : (13/45 : ℝ)≤d) (he : d≤(13/40 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(399872/297675 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_440 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (25/32 : ℝ)≤t) (hu : t≤(13/16 : ℝ))
    (hd : (13/45 : ℝ)≤d) (he : d≤(221/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(1542992/1233225 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_441 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (25/32 : ℝ)≤t) (hu : t≤(13/16 : ℝ))
    (hd : (221/720 : ℝ)≤d) (he : d≤(13/40 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(1420298/1233225 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_442 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (25/32 : ℝ)≤t) (hu : t≤(13/16 : ℝ))
    (hd : (13/45 : ℝ)≤d) (he : d≤(13/40 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (221/720 : ℝ) with hm|hm
  · exact corner_grid_440 h hl hu hd hm
  · exact corner_grid_441 h hl hu hm.le he

private lemma corner_grid_443 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/4 : ℝ)≤t) (hu : t≤(13/16 : ℝ))
    (hd : (13/45 : ℝ)≤d) (he : d≤(13/40 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (25/32 : ℝ) with hm|hm
  · exact corner_grid_439 h hl hm hd he
  · exact corner_grid_442 h hm.le hu hd he

private lemma corner_grid_444 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/4 : ℝ)≤t) (hu : t≤(25/32 : ℝ))
    (hd : (13/40 : ℝ)≤d) (he : d≤(247/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(3872/3325 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_445 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/4 : ℝ)≤t) (hu : t≤(25/32 : ℝ))
    (hd : (247/720 : ℝ)≤d) (he : d≤(13/36 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(6036008/5655825 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_446 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/4 : ℝ)≤t) (hu : t≤(25/32 : ℝ))
    (hd : (13/40 : ℝ)≤d) (he : d≤(13/36 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (247/720 : ℝ) with hm|hm
  · exact corner_grid_444 h hl hu hd hm
  · exact corner_grid_445 h hl hu hm.le he

private lemma corner_grid_447 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (25/32 : ℝ)≤t) (hu : t≤(13/16 : ℝ))
    (hd : (13/40 : ℝ)≤d) (he : d≤(247/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(15928/15225 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_448 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (25/32 : ℝ)≤t) (hu : t≤(13/16 : ℝ))
    (hd : (247/720 : ℝ)≤d) (he : d≤(13/36 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(1152602/1233225 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_449 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (25/32 : ℝ)≤t) (hu : t≤(13/16 : ℝ))
    (hd : (13/40 : ℝ)≤d) (he : d≤(13/36 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (247/720 : ℝ) with hm|hm
  · exact corner_grid_447 h hl hu hd hm
  · exact corner_grid_448 h hl hu hm.le he

private lemma corner_grid_450 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/4 : ℝ)≤t) (hu : t≤(13/16 : ℝ))
    (hd : (13/40 : ℝ)≤d) (he : d≤(13/36 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (25/32 : ℝ) with hm|hm
  · exact corner_grid_446 h hl hm hd he
  · exact corner_grid_449 h hm.le hu hd he

private lemma corner_grid_451 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/4 : ℝ)≤t) (hu : t≤(13/16 : ℝ))
    (hd : (13/45 : ℝ)≤d) (he : d≤(13/36 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (13/40 : ℝ) with hm|hm
  · exact corner_grid_443 h hl hu hd hm
  · exact corner_grid_450 h hl hu hm.le he

private lemma corner_grid_452 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (13/16 : ℝ)≤t) (hu : t≤(27/32 : ℝ))
    (hd : (13/45 : ℝ)≤d) (he : d≤(221/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(4746368/4181625 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_453 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (13/16 : ℝ)≤t) (hu : t≤(27/32 : ℝ))
    (hd : (221/720 : ℝ)≤d) (he : d≤(13/40 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(4255592/4181625 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_454 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (13/16 : ℝ)≤t) (hu : t≤(27/32 : ℝ))
    (hd : (13/45 : ℝ)≤d) (he : d≤(13/40 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (221/720 : ℝ) with hm|hm
  · exact corner_grid_452 h hl hu hd hm
  · exact corner_grid_453 h hl hu hm.le he

private lemma corner_grid_455 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (27/32 : ℝ)≤t) (hu : t≤(7/8 : ℝ))
    (hd : (13/45 : ℝ)≤d) (he : d≤(221/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(207548/212625 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_456 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (27/32 : ℝ)≤t) (hu : t≤(7/8 : ℝ))
    (hd : (221/720 : ℝ)≤d) (he : d≤(13/40 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(353749/425250 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_457 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (27/32 : ℝ)≤t) (hu : t≤(7/8 : ℝ))
    (hd : (13/45 : ℝ)≤d) (he : d≤(13/40 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (221/720 : ℝ) with hm|hm
  · exact corner_grid_455 h hl hu hd hm
  · exact corner_grid_456 h hl hu hm.le he

private lemma corner_grid_458 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (13/16 : ℝ)≤t) (hu : t≤(7/8 : ℝ))
    (hd : (13/45 : ℝ)≤d) (he : d≤(13/40 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (27/32 : ℝ) with hm|hm
  · exact corner_grid_454 h hl hm hd he
  · exact corner_grid_457 h hm.le hu hd he

private lemma corner_grid_459 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (13/16 : ℝ)≤t) (hu : t≤(27/32 : ℝ))
    (hd : (13/40 : ℝ)≤d) (he : d≤(247/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(46112/51625 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_460 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (13/16 : ℝ)≤t) (hu : t≤(27/32 : ℝ))
    (hd : (247/720 : ℝ)≤d) (he : d≤(13/36 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(3184808/4181625 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_461 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (13/16 : ℝ)≤t) (hu : t≤(27/32 : ℝ))
    (hd : (13/40 : ℝ)≤d) (he : d≤(13/36 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (247/720 : ℝ) with hm|hm
  · exact corner_grid_459 h hl hu hd hm
  · exact corner_grid_460 h hl hu hm.le he

private lemma corner_grid_462 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (27/32 : ℝ)≤t) (hu : t≤(7/8 : ℝ))
    (hd : (13/40 : ℝ)≤d) (he : d≤(247/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(594/875 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_463 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (27/32 : ℝ)≤t) (hu : t≤(7/8 : ℝ))
    (hd : (247/720 : ℝ)≤d) (he : d≤(13/36 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(219901/425250 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_464 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (27/32 : ℝ)≤t) (hu : t≤(7/8 : ℝ))
    (hd : (13/40 : ℝ)≤d) (he : d≤(13/36 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (247/720 : ℝ) with hm|hm
  · exact corner_grid_462 h hl hu hd hm
  · exact corner_grid_463 h hl hu hm.le he

private lemma corner_grid_465 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (13/16 : ℝ)≤t) (hu : t≤(7/8 : ℝ))
    (hd : (13/40 : ℝ)≤d) (he : d≤(13/36 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (27/32 : ℝ) with hm|hm
  · exact corner_grid_461 h hl hm hd he
  · exact corner_grid_464 h hm.le hu hd he

private lemma corner_grid_466 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (13/16 : ℝ)≤t) (hu : t≤(7/8 : ℝ))
    (hd : (13/45 : ℝ)≤d) (he : d≤(13/36 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (13/40 : ℝ) with hm|hm
  · exact corner_grid_458 h hl hu hd hm
  · exact corner_grid_465 h hl hu hm.le he

private lemma corner_grid_467 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/4 : ℝ)≤t) (hu : t≤(7/8 : ℝ))
    (hd : (13/45 : ℝ)≤d) (he : d≤(13/36 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (13/16 : ℝ) with hm|hm
  · exact corner_grid_451 h hl hm hd he
  · exact corner_grid_466 h hm.le hu hd he

private lemma corner_grid_468 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/4 : ℝ)≤t) (hu : t≤(25/32 : ℝ))
    (hd : (13/36 : ℝ)≤d) (he : d≤(91/240 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(218240/226233 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_469 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/4 : ℝ)≤t) (hu : t≤(25/32 : ℝ))
    (hd : (91/240 : ℝ)≤d) (he : d≤(143/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(538472/628425 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_470 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/4 : ℝ)≤t) (hu : t≤(25/32 : ℝ))
    (hd : (13/36 : ℝ)≤d) (he : d≤(143/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (91/240 : ℝ) with hm|hm
  · exact corner_grid_468 h hl hu hd hm
  · exact corner_grid_469 h hl hu hm.le he

private lemma corner_grid_471 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (25/32 : ℝ)≤t) (hu : t≤(13/16 : ℝ))
    (hd : (13/36 : ℝ)≤d) (he : d≤(91/240 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(40304/49329 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_472 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (25/32 : ℝ)≤t) (hu : t≤(13/16 : ℝ))
    (hd : (91/240 : ℝ)≤d) (he : d≤(143/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(13574/19575 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_473 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (25/32 : ℝ)≤t) (hu : t≤(13/16 : ℝ))
    (hd : (13/36 : ℝ)≤d) (he : d≤(143/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (91/240 : ℝ) with hm|hm
  · exact corner_grid_471 h hl hu hd hm
  · exact corner_grid_472 h hl hu hm.le he

private lemma corner_grid_474 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/4 : ℝ)≤t) (hu : t≤(13/16 : ℝ))
    (hd : (13/36 : ℝ)≤d) (he : d≤(143/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (25/32 : ℝ) with hm|hm
  · exact corner_grid_470 h hl hm hd he
  · exact corner_grid_473 h hm.le hu hd he

private lemma corner_grid_475 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/4 : ℝ)≤t) (hu : t≤(25/32 : ℝ))
    (hd : (143/360 : ℝ)≤d) (he : d≤(299/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(221408/297675 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_476 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/4 : ℝ)≤t) (hu : t≤(25/32 : ℝ))
    (hd : (299/720 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(3537512/5655825 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_477 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/4 : ℝ)≤t) (hu : t≤(25/32 : ℝ))
    (hd : (143/360 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (299/720 : ℝ) with hm|hm
  · exact corner_grid_475 h hl hu hd hm
  · exact corner_grid_476 h hl hu hm.le he

private lemma corner_grid_478 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (25/32 : ℝ)≤t) (hu : t≤(13/16 : ℝ))
    (hd : (143/360 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(695288/1233225 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_479 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/4 : ℝ)≤t) (hu : t≤(13/16 : ℝ))
    (hd : (143/360 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (25/32 : ℝ) with hm|hm
  · exact corner_grid_477 h hl hm hd he
  · exact corner_grid_478 h hm.le hu hd he

private lemma corner_grid_480 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/4 : ℝ)≤t) (hu : t≤(13/16 : ℝ))
    (hd : (13/36 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (143/360 : ℝ) with hm|hm
  · exact corner_grid_474 h hl hu hd hm
  · exact corner_grid_479 h hl hu hm.le he

private lemma corner_grid_481 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (13/16 : ℝ)≤t) (hu : t≤(27/32 : ℝ))
    (hd : (13/36 : ℝ)≤d) (he : d≤(91/240 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(104192/167265 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_482 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (13/16 : ℝ)≤t) (hu : t≤(27/32 : ℝ))
    (hd : (91/240 : ℝ)≤d) (he : d≤(143/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(221672/464625 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_483 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (13/16 : ℝ)≤t) (hu : t≤(27/32 : ℝ))
    (hd : (13/36 : ℝ)≤d) (he : d≤(143/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (91/240 : ℝ) with hm|hm
  · exact corner_grid_481 h hl hu hd hm
  · exact corner_grid_482 h hl hu hm.le he

private lemma corner_grid_484 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (27/32 : ℝ)≤t) (hu : t≤(7/8 : ℝ))
    (hd : (13/36 : ℝ)≤d) (he : d≤(143/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(2948/8505 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_485 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (13/16 : ℝ)≤t) (hu : t≤(7/8 : ℝ))
    (hd : (13/36 : ℝ)≤d) (he : d≤(143/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (27/32 : ℝ) with hm|hm
  · exact corner_grid_483 h hl hm hd he
  · exact corner_grid_484 h hm.le hu hd he

private lemma corner_grid_486 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (13/16 : ℝ)≤t) (hu : t≤(27/32 : ℝ))
    (hd : (143/360 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(1355552/4181625 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_487 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (27/32 : ℝ)≤t) (_hu : t≤(7/8 : ℝ))
    (hd : (143/360 : ℝ)≤d) (_he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  nlinarith only [h.dbound,h.d0,hd,hl]

private lemma corner_grid_488 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (13/16 : ℝ)≤t) (hu : t≤(7/8 : ℝ))
    (hd : (143/360 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (27/32 : ℝ) with hm|hm
  · exact corner_grid_486 h hl hm hd he
  · exact corner_grid_487 h hm.le hu hd he

private lemma corner_grid_489 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (13/16 : ℝ)≤t) (hu : t≤(7/8 : ℝ))
    (hd : (13/36 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (143/360 : ℝ) with hm|hm
  · exact corner_grid_485 h hl hu hd hm
  · exact corner_grid_488 h hl hu hm.le he

private lemma corner_grid_490 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/4 : ℝ)≤t) (hu : t≤(7/8 : ℝ))
    (hd : (13/36 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (13/16 : ℝ) with hm|hm
  · exact corner_grid_480 h hl hm hd he
  · exact corner_grid_489 h hm.le hu hd he

private lemma corner_grid_491 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/4 : ℝ)≤t) (hu : t≤(7/8 : ℝ))
    (hd : (13/45 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (13/36 : ℝ) with hm|hm
  · exact corner_grid_467 h hl hu hd hm
  · exact corner_grid_490 h hl hu hm.le he

private lemma corner_grid_492 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/8 : ℝ)≤t) (hu : t≤(29/32 : ℝ))
    (hd : (13/45 : ℝ)≤d) (he : d≤(221/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(1895168/2594025 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_493 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/8 : ℝ)≤t) (hu : t≤(29/32 : ℝ))
    (hd : (221/720 : ℝ)≤d) (he : d≤(13/40 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(1404392/2594025 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_494 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/8 : ℝ)≤t) (hu : t≤(29/32 : ℝ))
    (hd : (13/45 : ℝ)≤d) (he : d≤(13/40 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (221/720 : ℝ) with hm|hm
  · exact corner_grid_492 h hl hu hd hm
  · exact corner_grid_493 h hl hu hm.le he

private lemma corner_grid_495 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (29/32 : ℝ)≤t) (hu : t≤(15/16 : ℝ))
    (hd : (13/45 : ℝ)≤d) (he : d≤(13/40 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(117392/439425 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_496 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/8 : ℝ)≤t) (hu : t≤(15/16 : ℝ))
    (hd : (13/45 : ℝ)≤d) (he : d≤(13/40 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (29/32 : ℝ) with hm|hm
  · exact corner_grid_494 h hl hm hd he
  · exact corner_grid_495 h hm.le hu hd he

private lemma corner_grid_497 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/8 : ℝ)≤t) (hu : t≤(29/32 : ℝ))
    (hd : (13/40 : ℝ)≤d) (he : d≤(13/36 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(10912/32025 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_498 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (29/32 : ℝ)≤t) (_hu : t≤(15/16 : ℝ))
    (hd : (13/40 : ℝ)≤d) (_he : d≤(13/36 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  nlinarith only [h.dbound,h.d0,hd,hl]

private lemma corner_grid_499 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/8 : ℝ)≤t) (hu : t≤(15/16 : ℝ))
    (hd : (13/40 : ℝ)≤d) (he : d≤(13/36 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (29/32 : ℝ) with hm|hm
  · exact corner_grid_497 h hl hm hd he
  · exact corner_grid_498 h hm.le hu hd he

private lemma corner_grid_500 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/8 : ℝ)≤t) (hu : t≤(15/16 : ℝ))
    (hd : (13/45 : ℝ)≤d) (he : d≤(13/36 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (13/40 : ℝ) with hm|hm
  · exact corner_grid_496 h hl hu hd hm
  · exact corner_grid_499 h hl hu hm.le he

private lemma corner_grid_501 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (15/16 : ℝ)≤t) (_hu : t≤(1/1 : ℝ))
    (hd : (13/45 : ℝ)≤d) (_he : d≤(13/36 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  nlinarith only [h.dbound,h.d0,hd,hl]

private lemma corner_grid_502 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/8 : ℝ)≤t) (hu : t≤(1/1 : ℝ))
    (hd : (13/45 : ℝ)≤d) (he : d≤(13/36 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (15/16 : ℝ) with hm|hm
  · exact corner_grid_500 h hl hm hd he
  · exact corner_grid_501 h hm.le hu hd he

private lemma corner_grid_503 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/8 : ℝ)≤t) (_hu : t≤(1/1 : ℝ))
    (hd : (13/36 : ℝ)≤d) (_he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  nlinarith only [h.dbound,h.d0,hd,hl]

private lemma corner_grid_504 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/8 : ℝ)≤t) (hu : t≤(1/1 : ℝ))
    (hd : (13/45 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (13/36 : ℝ) with hm|hm
  · exact corner_grid_502 h hl hu hd hm
  · exact corner_grid_503 h hl hu hm.le he

private lemma corner_grid_505 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/4 : ℝ)≤t) (hu : t≤(1/1 : ℝ))
    (hd : (13/45 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (7/8 : ℝ) with hm|hm
  · exact corner_grid_491 h hl hm hd he
  · exact corner_grid_504 h hm.le hu hd he

private lemma corner_grid_506 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/4 : ℝ)≤t) (hu : t≤(25/32 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(169/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(45056/89775 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_507 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (25/32 : ℝ)≤t) (hu : t≤(13/16 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(169/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(39248/137025 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_508 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/4 : ℝ)≤t) (hu : t≤(13/16 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(169/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (25/32 : ℝ) with hm|hm
  · exact corner_grid_506 h hl hm hd he
  · exact corner_grid_507 h hm.le hu hd he

private lemma corner_grid_509 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/4 : ℝ)≤t) (hu : t≤(25/32 : ℝ))
    (hd : (169/360 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(1351328/5655825 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_510 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (25/32 : ℝ)≤t) (_hu : t≤(13/16 : ℝ))
    (hd : (169/360 : ℝ)≤d) (_he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  nlinarith only [h.dbound,h.d0,hd,hl]

private lemma corner_grid_511 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/4 : ℝ)≤t) (hu : t≤(13/16 : ℝ))
    (hd : (169/360 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (25/32 : ℝ) with hm|hm
  · exact corner_grid_509 h hl hm hd he
  · exact corner_grid_510 h hm.le hu hd he

private lemma corner_grid_512 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/4 : ℝ)≤t) (hu : t≤(13/16 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (169/360 : ℝ) with hm|hm
  · exact corner_grid_508 h hl hu hd hm
  · exact corner_grid_511 h hl hu hm.le he

private lemma corner_grid_513 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (13/16 : ℝ)≤t) (_hu : t≤(7/8 : ℝ))
    (hd : (13/30 : ℝ)≤d) (_he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  nlinarith only [h.dbound,h.d0,hd,hl]

private lemma corner_grid_514 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/4 : ℝ)≤t) (hu : t≤(7/8 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (13/16 : ℝ) with hm|hm
  · exact corner_grid_512 h hl hm hd he
  · exact corner_grid_513 h hm.le hu hd he

private lemma corner_grid_515 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/4 : ℝ)≤t) (_hu : t≤(7/8 : ℝ))
    (hd : (91/180 : ℝ)≤d) (_he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  nlinarith only [h.dbound,h.d0,hd,hl]

private lemma corner_grid_516 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/4 : ℝ)≤t) (hu : t≤(7/8 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (91/180 : ℝ) with hm|hm
  · exact corner_grid_514 h hl hu hd hm
  · exact corner_grid_515 h hl hu hm.le he

private lemma corner_grid_517 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/8 : ℝ)≤t) (_hu : t≤(1/1 : ℝ))
    (hd : (13/30 : ℝ)≤d) (_he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  nlinarith only [h.dbound,h.d0,hd,hl]

private lemma corner_grid_518 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/4 : ℝ)≤t) (hu : t≤(1/1 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (7/8 : ℝ) with hm|hm
  · exact corner_grid_516 h hl hm hd he
  · exact corner_grid_517 h hm.le hu hd he

private lemma corner_grid_519 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/4 : ℝ)≤t) (hu : t≤(1/1 : ℝ))
    (hd : (13/45 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (13/30 : ℝ) with hm|hm
  · exact corner_grid_505 h hl hu hd hm
  · exact corner_grid_518 h hl hu hm.le he

private lemma corner_grid_520 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/2 : ℝ)≤t) (hu : t≤(1/1 : ℝ))
    (hd : (13/45 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (3/4 : ℝ) with hm|hm
  · exact corner_grid_438 h hl hm hd he
  · exact corner_grid_519 h hm.le hu hd he

private lemma corner_grid_521 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/2 : ℝ)≤t) (hu : t≤(1/1 : ℝ))
    (hd : (0/1 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (13/45 : ℝ) with hm|hm
  · exact corner_grid_269 h hl hu hd hm
  · exact corner_grid_520 h hl hu hm.le he

private lemma corner_grid_522 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (0/1 : ℝ)≤t) (hu : t≤(1/1 : ℝ))
    (hd : (0/1 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (1/2 : ℝ) with hm|hm
  · exact corner_grid_202 h hl hm hd he
  · exact corner_grid_521 h hm.le hu hd he

theorem corner_root_strict {t d x : ℝ} (h : CornerRootData t d x) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  exact corner_grid_522 h (by simpa using h.t0) (by simpa using h.t1.le) (by simpa using h.d0) (by nlinarith only [h.d0,h.d3])
end CubicTorus

end
end

end OAI
